/*
  TAK-Client-UDP-ESP8266

  上电后 ESP8266 自己开一个 WiFi 热点。手机连上这个热点后，
  位置和聊天是分开的：

      SA 位置        239.2.3.1:6969          UDP 组播
      All Chat Rooms 224.10.10.1:17012       UDP 组播
      私聊           本机 IP:17012            UDP 单播

  本机把自身位置写成 CoT，经 UDP 发给同一热点上的 ATAK。
  没有 TAK Server，位置、群聊和私聊都在本地网络里完成。

  手机侧：
    1. 连接下面配置的热点
    2. 系统提示“无互联网”时选择保持连接
    3. 打开 ATAK，不要连接 TAK Server
       位置走 239.2.3.1:6969
       群聊走 224.10.10.1:17012，私聊走单播 UDP 17012
    4. 浏览器打开 http://192.168.4.1 可改呼号、小队颜色和角色，保存后一直有效

  本机没有 GPS。经纬度可在配置页修改，未保存时默认为 31.230416, 121.473701。
  时钟在收到第一条带时间的 ATAK 报文后自动对齐，
  对齐前发出的位置会被 ATAK 当成过期数据丢掉。

  收到 GeoChat 文本聊天（CoT 类型 b-t-f，正文在 remarks）时，
  串口打印发送者、聊天室和内容。
  聊天正文里出现 Roger 会闪板载灯，出现 callRESTART 会重启。
  私聊里出现“开灯 / 打开灯 / turn on”等文字时 IO5 输出高电平，并回复“收到，已开灯”；
  出现“关灯 / 关闭灯 / 关掉灯 / turn off”等文字时 IO5 输出低电平，并回复“收到，已关灯”。
  其他私聊内容只回复“收到”。私聊发送“状态”时，回复呼号、小队、角色、经纬度、灯的开关和运行时间。
  回复发回对方的 UDP 17012。
  IO4 接按键，另一端接 GND。按下后向最近一次私聊对象发送“你好”。
*/

#include <ESP8266WiFi.h>
#include <ESP8266WebServer.h>
#include <EEPROM.h>
#include <WiFiUdp.h>
#include <lwip/igmp.h>
#include <lwip/netif.h>
#include <stdlib_noniso.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

// -------------------- 热点 --------------------
static const char* AP_SSID = "TAK-Client-UDP-ESP8266";
static const char* AP_PASS = "12345678";  // 至少 8 位；改成 "" 则开放热点
static const int AP_CHANNEL = 6;
static const int AP_MAX_CLIENTS = 8;

static const IPAddress AP_IP(192, 168, 4, 1);
static const IPAddress AP_GATEWAY(192, 168, 4, 1);
static const IPAddress AP_MASK(255, 255, 255, 0);

// -------------------- ATAK SA 组播 --------------------
static const IPAddress SA_MCAST(239, 2, 3, 1);
static const uint16_t SA_PORT = 6969;
static const IPAddress CHAT_MCAST(224, 10, 10, 1);
static const uint16_t CHAT_PORT = 17012;
static const uint32_t SEND_INTERVAL_MS = 5000;
static const time_t STALE_AFTER_SEC = 45;

// 没有 GPS。未在网页保存坐标时使用。
static char cfgLat[16] = "31.230416";
static char cfgLon[16] = "121.473701";
static const char* DEVICE_HAE = "0.0";

// 没保存过配置时使用。之后以网页里保存的为准。
static char cfgCallsign[24] = "ESP8266-TAK";
static char cfgTeam[16] = "Cyan";
static char cfgRole[24] = "Team Member";

// 还没从 ATAK 报文对时之前使用的 UTC。2026-10-06 00:00:00。
static const time_t BOOT_UNIX = 1791244800;

static const int RX_MAX = 1460;
static const int LAMP_PIN = 5;     // IO5，高电平亮，低电平灭
static const int BUTTON_PIN = 4;   // IO4，按键另一端接 GND，内部上拉

// -------------------- 运行状态 --------------------
static WiFiUDP rxUdp;
static WiFiUDP txUdp;
static WiFiUDP chatUdp;

static char deviceUid[28];
static bool saJoined = false;
static bool chatJoined = false;
static bool clockSynced = false;
static time_t clockBase = BOOT_UNIX;
static uint32_t clockBaseMs = 0;
static uint32_t nextSendMs = 0;
static uint32_t nextJoinMs = 0;
static uint32_t ledOffAt = 0;
static uint8_t lastClients = 0;
static IPAddress lastPeerIp;
static char lastPeerCallsign[32] = "ATAK";
static char lastPeerUid[48] = "ATAK";
static bool hasLastPeer = false;

// -------------------- 时间 --------------------
static time_t civilToUnix(int y, int m, int d, int hh, int mm, int ss) {
  y -= m <= 2;
  const int era = (y >= 0 ? y : y - 399) / 400;
  const unsigned yoe = (unsigned)(y - era * 400);
  const unsigned doy = (153 * (m + (m > 2 ? -3 : 9)) + 2) / 5 + d - 1;
  const unsigned doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
  const long days = (long)era * 146097L + (long)doe - 719468L;
  return (time_t)(days * 86400L + hh * 3600L + mm * 60L + ss);
}

static time_t currentUnix() {
  return clockBase + (time_t)((millis() - clockBaseMs) / 1000UL);
}

static void syncClock(time_t t) {
  clockBase = t;
  clockBaseMs = millis();
  clockSynced = true;
}

static void formatCotTime(char* out, size_t n, time_t t) {
  struct tm parts;
  if (gmtime_r(&t, &parts) == nullptr) {
    snprintf(out, n, "1970-01-01T00:00:00.000Z");
    return;
  }
  strftime(out, n, "%Y-%m-%dT%H:%M:%S.000Z", &parts);
}

// -------------------- 组播 --------------------
// softAP 网卡有时没带 IGMP 标志，beginMulticast 会直接失败。
static void enableApIgmp(const IPAddress& apIp) {
  ip4_addr_t want;
  ip4_addr_set_u32(&want, (uint32_t)apIp);

  struct netif* nif;
  NETIF_FOREACH(nif) {
    if (!ip4_addr_cmp(netif_ip4_addr(nif), &want)) {
      continue;
    }
    if (nif->flags & NETIF_FLAG_IGMP) {
      return;
    }
    nif->flags |= NETIF_FLAG_IGMP;
    if (igmp_start(nif) == ERR_OK) {
      Serial.println("已在 AP 网卡启用 IGMP");
    } else {
      Serial.println("AP 网卡 IGMP 启用失败");
    }
    return;
  }
  Serial.println("未找到 AP 网卡，仍尝试加入组播");
}

static bool joinMulticast(WiFiUDP& udp, const IPAddress& group, uint16_t port, const char* name) {
  IPAddress ip = WiFi.softAPIP();
  if (ip == IPAddress(0, 0, 0, 0)) {
    return false;
  }
  enableApIgmp(ip);
  if (!udp.beginMulticast(ip, group, port)) {
    Serial.print("加入 ");
    Serial.print(name);
    Serial.println(" 失败，稍后重试");
    return false;
  }
  Serial.print("已加入 ");
  Serial.println(name);
  return true;
}

static void joinGroups() {
  if (!saJoined) {
    saJoined = joinMulticast(rxUdp, SA_MCAST, SA_PORT, "SA 239.2.3.1:6969");
  }
  if (!chatJoined) {
    // beginMulticast 绑在 0.0.0.0:17012，同一套接字同时收到群聊组播和私聊单播。
    chatJoined = joinMulticast(chatUdp, CHAT_MCAST, CHAT_PORT, "聊天 224.10.10.1:17012 + 单播 17012");
  }
}

// -------------------- 发送本机位置 --------------------
static bool sendSa() {
  IPAddress ip = WiFi.softAPIP();
  if (ip == IPAddress(0, 0, 0, 0)) {
    return false;
  }

  char nowText[32];
  char staleText[32];
  time_t now = currentUnix();
  formatCotTime(nowText, sizeof(nowText), now);
  formatCotTime(staleText, sizeof(staleText), now + STALE_AFTER_SEC);

  static char cot[1024];
  int len = snprintf(
      cot, sizeof(cot),
      "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>"
      "<event version=\"2.0\" uid=\"%s\" type=\"a-f-G-U-C-I\" "
      "time=\"%s\" start=\"%s\" stale=\"%s\" how=\"h-g-i-g-o\">"
      "<point lat=\"%s\" lon=\"%s\" hae=\"%s\" ce=\"9999999.0\" le=\"9999999.0\"/>"
      "<detail>"
      "<takv version=\"1.0\" platform=\"ATAK-CIV\" os=\"ESP8266\" device=\"ESP8266\"/>"
      "<contact callsign=\"%s\" endpoint=\"%u.%u.%u.%u:%u:udp\"/>"
      "<uid Droid=\"%s\"/>"
      "<__group name=\"%s\" role=\"%s\"/>"
      "<status battery=\"100\"/>"
      "<track course=\"0.0\" speed=\"0.0\"/>"
      "</detail></event>",
      deviceUid, nowText, nowText, staleText, cfgLat, cfgLon, DEVICE_HAE, cfgCallsign,
      AP_IP[0], AP_IP[1], AP_IP[2], AP_IP[3], (unsigned)CHAT_PORT, cfgCallsign, cfgTeam, cfgRole);

  if (len <= 0 || len >= (int)sizeof(cot)) {
    Serial.println("CoT 组包失败");
    return false;
  }

  if (!txUdp.beginPacketMulticast(SA_MCAST, SA_PORT, ip, 1)) {
    Serial.println("组播发送失败: beginPacket");
    return false;
  }
  txUdp.write((const uint8_t*)cot, len);
  if (!txUdp.endPacket()) {
    Serial.println("组播发送失败: endPacket");
    return false;
  }

  Serial.printf("已发送 %s  %s,%s  %s  客户端 %u\n", cfgCallsign, cfgLat, cfgLon,
                clockSynced ? "已对时" : "未对时", WiFi.softAPgetStationNum());
  return true;
}

// -------------------- 接收 --------------------
static const char* findBytes(const char* hay, int hayLen, const char* needle) {
  int n = (int)strlen(needle);
  if (n <= 0 || hayLen < n) {
    return nullptr;
  }
  for (int i = 0; i <= hayLen - n; i++) {
    if (memcmp(hay + i, needle, n) == 0) {
      return hay + i;
    }
  }
  return nullptr;
}

static bool xmlAttr(const char* xml, const char* key, char* out, size_t outLen) {
  if (xml == nullptr || key == nullptr || out == nullptr || outLen == 0) {
    return false;
  }
  size_t keyLen = strlen(key);
  const char* p = xml;
  while ((p = strstr(p, key)) != nullptr) {
    bool boundary = (p == xml);
    if (!boundary) {
      char prev = p[-1];
      boundary = !((prev >= 'A' && prev <= 'Z') || (prev >= 'a' && prev <= 'z') || prev == '_' ||
                   (prev >= '0' && prev <= '9'));
    }
    if (boundary && strncmp(p + keyLen, "=\"", 2) == 0) {
      const char* start = p + keyLen + 2;
      const char* end = strchr(start, '"');
      if (end == nullptr) {
        return false;
      }
      size_t n = (size_t)(end - start);
      if (n >= outLen) {
        n = outLen - 1;
      }
      memcpy(out, start, n);
      out[n] = '\0';
      return true;
    }
    p += keyLen == 0 ? 1 : keyLen;
  }
  return false;
}

// ATAK 聊天正文里的 &lt; &amp; 等转回原文。中文本身是 UTF-8，按字节拷贝。
static size_t copyUnescaped(const char* src, size_t srcLen, char* out, size_t outLen) {
  size_t i = 0;
  size_t o = 0;
  while (i < srcLen && (src[i] == ' ' || src[i] == '\n' || src[i] == '\r' || src[i] == '\t')) {
    i++;
  }
  if (srcLen - i >= 12 && memcmp(src + i, "<![CDATA[", 9) == 0) {
    i += 9;
    if (srcLen >= 3 && memcmp(src + srcLen - 3, "]]>", 3) == 0) {
      srcLen -= 3;
    }
  }
  while (i < srcLen && o + 1 < outLen) {
    if (src[i] == '&') {
      char decoded = 0;
      size_t used = 0;
      if (i + 4 <= srcLen && memcmp(src + i, "&lt;", 4) == 0) {
        decoded = '<';
        used = 4;
      } else if (i + 4 <= srcLen && memcmp(src + i, "&gt;", 4) == 0) {
        decoded = '>';
        used = 4;
      } else if (i + 5 <= srcLen && memcmp(src + i, "&amp;", 5) == 0) {
        decoded = '&';
        used = 5;
      } else if (i + 6 <= srcLen && memcmp(src + i, "&quot;", 6) == 0) {
        decoded = '"';
        used = 6;
      } else if (i + 6 <= srcLen && memcmp(src + i, "&apos;", 6) == 0) {
        decoded = '\'';
        used = 6;
      }
      if (used != 0) {
        out[o++] = decoded;
        i += used;
        continue;
      }
    }
    out[o++] = src[i++];
  }
  while (o > 0 && (out[o - 1] == ' ' || out[o - 1] == '\n' || out[o - 1] == '\r' || out[o - 1] == '\t')) {
    o--;
  }
  out[o] = '\0';
  return o;
}

static bool extractRemarks(const char* xml, char* out, size_t outLen) {
  const char* open = strstr(xml, "<remarks");
  if (open == nullptr) {
    return false;
  }
  const char* gt = strchr(open, '>');
  if (gt == nullptr || (gt > open && gt[-1] == '/')) {
    return false;
  }
  const char* close = strstr(gt + 1, "</remarks>");
  if (close == nullptr) {
    return false;
  }
  return copyUnescaped(gt + 1, (size_t)(close - (gt + 1)), out, outLen) > 0;
}

static bool isGeoChat(const char* xml) {
  char type[24];
  if (xmlAttr(xml, "type", type, sizeof(type)) && strncmp(type, "b-t-f", 5) == 0) {
    return true;
  }
  if (strstr(xml, "<__chat") != nullptr) {
    return true;
  }
  return strstr(xml, "senderCallsign=\"") != nullptr && strstr(xml, "<remarks") != nullptr;
}

static void flashLed(uint32_t ms);

static void applyChatCommands(const char* body) {
  if (strstr(body, "callRESTART") != nullptr) {
    Serial.println("收到 callRESTART，正在重启");
    Serial.flush();
    delay(100);
    ESP.restart();
  }
  if (strstr(body, "Roger") != nullptr) {
    Serial.println("收到 Roger");
    flashLed(800);
  }
}

static bool printGeoChat(const char* xml) {
  if (!isGeoChat(xml)) {
    return false;
  }
  static char body[640];
  if (!extractRemarks(xml, body, sizeof(body))) {
    return false;
  }

  char sender[40];
  char room[64];
  if (!xmlAttr(xml, "senderCallsign", sender, sizeof(sender))) {
    if (!xmlAttr(xml, "callsign", sender, sizeof(sender))) {
      snprintf(sender, sizeof(sender), "未知");
    }
  }
  if (!xmlAttr(xml, "chatroom", room, sizeof(room))) {
    snprintf(room, sizeof(room), "未知");
  }

  Serial.print("[聊天] 发送者=");
  Serial.print(sender);
  Serial.print(" 房间=");
  Serial.println(room);
  Serial.println(body);
  applyChatCommands(body);
  return true;
}

// TAK protobuf 的 detail 里经常仍夹着一段 XML 聊天。按字节找，不在 0x00 处停。
static bool printEmbeddedChat(const uint8_t* data, int len) {
  const char* begin = findBytes((const char*)data, len, "<__chat");
  if (begin == nullptr) {
    begin = findBytes((const char*)data, len, "<remarks");
  }
  if (begin == nullptr) {
    return false;
  }
  int offset = (int)(begin - (const char*)data);
  const char* end = findBytes(begin, len - offset, "</remarks>");
  if (end == nullptr) {
    return false;
  }
  end += strlen("</remarks>");
  int n = (int)(end - begin);
  if (n <= 0 || n > RX_MAX) {
    return false;
  }
  static char frag[RX_MAX + 1];
  memcpy(frag, begin, n);
  frag[n] = '\0';
  return printGeoChat(frag);
}

static void maybeSyncClock(const char* xml) {
  const char* p = strstr(xml, "time=\"");
  if (p == nullptr) {
    return;
  }
  int y, mo, d, h, mi, s;
  if (sscanf(p, "time=\"%d-%d-%dT%d:%d:%d", &y, &mo, &d, &h, &mi, &s) != 6) {
    return;
  }
  // ESP8266 的 time_t 是 32 位，2038 年以后会溢出。
  if (y < 2020 || y > 2037 || mo < 1 || mo > 12 || d < 1 || d > 31) {
    return;
  }
  time_t incoming = civilToUnix(y, mo, d, h, mi, s);
  if (clockSynced && incoming <= currentUnix() + 2) {
    return;
  }
  bool was = clockSynced;
  syncClock(incoming);
  if (!was) {
    Serial.printf("已用 ATAK 报文对时: %04d-%02d-%02d %02d:%02d:%02dZ\n", y, mo, d, h, mi, s);
    nextSendMs = millis();
  }
}

static void printIp(const IPAddress& ip) {
  Serial.printf("%u.%u.%u.%u", ip[0], ip[1], ip[2], ip[3]);
}

static void flashLed(uint32_t ms) {
  digitalWrite(LED_BUILTIN, LOW);
  ledOffAt = millis() + ms;
}

static void serviceLed() {
  if (ledOffAt != 0 && (int32_t)(millis() - ledOffAt) >= 0) {
    digitalWrite(LED_BUILTIN, HIGH);
    ledOffAt = 0;
  }
}

static void handleText(char* text, int len, const IPAddress& from, uint16_t port) {
  char eventUid[48];
  if (xmlAttr(text, "uid", eventUid, sizeof(eventUid)) && strcmp(eventUid, deviceUid) == 0) {
    return;
  }

  maybeSyncClock(text);

  char callsign[32];
  char type[32];
  bool hasCallsign = xmlAttr(text, "callsign", callsign, sizeof(callsign));
  bool hasType = xmlAttr(text, "type", type, sizeof(type));
  Serial.printf("收到 %d 字节  来自 ", len);
  printIp(from);
  Serial.printf(":%u", port);
  if (hasCallsign) {
    Serial.printf("  callsign=%s", callsign);
  }
  if (hasType) {
    Serial.printf("  type=%s", type);
  }
  Serial.println();
  printGeoChat(text);
}

static void printRawPacket(const char* channel, const uint8_t* data, int len, int packetSize, const IPAddress& from,
                           uint16_t port, const IPAddress& dest) {
  Serial.println();
  Serial.print("======== ");
  Serial.print(channel);
  Serial.print(" 收到 ");
  Serial.print(packetSize);
  Serial.print(" 字节  ");
  printIp(from);
  Serial.print(":");
  Serial.print(port);
  Serial.print(" -> ");
  printIp(dest);
  Serial.println(" ========");
  if (len > 0) {
    Serial.write(data, len);
  }
  if (len <= 0 || data[len - 1] != '\n') {
    Serial.println();
  }
  if (packetSize > len) {
    Serial.print("（只打印了前 ");
    Serial.print(len);
    Serial.println(" 字节）");
  }
  Serial.println("======== 结束 ========");
}

static int lastMatch(const uint8_t* data, int len, const char* word) {
  int n = (int)strlen(word);
  if (n <= 0 || len < n) {
    return -1;
  }
  int last = -1;
  for (int i = 0; i <= len - n; i++) {
    bool same = true;
    for (int j = 0; j < n; j++) {
      unsigned char a = data[i + j];
      unsigned char b = (unsigned char)word[j];
      if (a >= 'A' && a <= 'Z') {
        a = (unsigned char)(a - 'A' + 'a');
      }
      if (b >= 'A' && b <= 'Z') {
        b = (unsigned char)(b - 'A' + 'a');
      }
      if (a != b) {
        same = false;
        break;
      }
    }
    if (same) {
      last = i;
    }
  }
  return last;
}

static int latestWord(const uint8_t* data, int len, const char* const* words, int count) {
  int best = -1;
  for (int i = 0; i < count; i++) {
    int at = lastMatch(data, len, words[i]);
    if (at > best) {
      best = at;
    }
  }
  return best;
}

// 1 开灯，-1 关灯，0 不是开关灯指令。
static int applyLampCommand(const uint8_t* data, int len) {
  static const char* onWords[] = {"开灯",     "打开灯", "灯打开", "把灯打开", "开下灯", "开一下灯",
                                  "turn on", "light on", "led on"};
  static const char* offWords[] = {"关灯",     "关闭灯", "关掉灯", "灯关闭", "灯关掉", "把灯关",
                                   "turn off", "light off", "led off"};
  int onAt = latestWord(data, len, onWords, (int)(sizeof(onWords) / sizeof(onWords[0])));
  int offAt = latestWord(data, len, offWords, (int)(sizeof(offWords) / sizeof(offWords[0])));
  if (onAt < 0 && offAt < 0) {
    return 0;
  }
  if (offAt > onAt) {
    digitalWrite(LAMP_PIN, LOW);
    Serial.println("IO5 关灯");
    return -1;
  }
  digitalWrite(LAMP_PIN, HIGH);
  Serial.println("IO5 开灯");
  return 1;
}

static bool extractQuoted(const uint8_t* data, int len, const char* key, char* out, size_t outLen) {
  int keyLen = (int)strlen(key);
  if (keyLen <= 0 || outLen == 0) {
    return false;
  }
  for (int i = 0; i + keyLen + 2 < len; i++) {
    if (i > 0) {
      unsigned char prev = data[i - 1];
      if ((prev >= 'A' && prev <= 'Z') || (prev >= 'a' && prev <= 'z') || prev == '_' ||
          (prev >= '0' && prev <= '9')) {
        continue;
      }
    }
    if (memcmp(data + i, key, keyLen) != 0 || data[i + keyLen] != '=' || data[i + keyLen + 1] != '"') {
      continue;
    }
    int start = i + keyLen + 2;
    int end = start;
    while (end < len && data[end] != '"' && data[end] != 0) {
      end++;
    }
    if (end >= len || data[end] != '"') {
      return false;
    }
    size_t n = (size_t)(end - start);
    if (n == 0 || n >= outLen) {
      return false;
    }
    memcpy(out, data + start, n);
    out[n] = '\0';
    return true;
  }
  return false;
}

static bool xmlSafeToken(const char* s) {
  if (s == nullptr || s[0] == '\0') {
    return false;
  }
  for (const char* p = s; *p; p++) {
    if (*p == '<' || *p == '>' || *p == '&' || *p == '"' || *p == '\'') {
      return false;
    }
  }
  return true;
}

static bool extractAndroidUid(const uint8_t* data, int len, char* out, size_t outLen) {
  const char* key = "ANDROID-";
  int keyLen = 8;
  for (int i = 0; i + keyLen < len; i++) {
    if (memcmp(data + i, key, keyLen) != 0) {
      continue;
    }
    int end = i + keyLen;
    while (end < len) {
      unsigned char c = data[end];
      bool hex = (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F') || c == '-';
      if (!hex) {
        break;
      }
      end++;
    }
    size_t n = (size_t)(end - i);
    if (n < 12 || n >= outLen) {
      continue;
    }
    memcpy(out, data + i, n);
    out[n] = '\0';
    return true;
  }
  return false;
}

static bool sendChatReply(const IPAddress& to, const char* text, const char* peerCallsign, const char* peerUid) {
  char nowText[32];
  char staleText[32];
  char eventUid[72];
  time_t now = currentUnix();
  formatCotTime(nowText, sizeof(nowText), now);
  formatCotTime(staleText, sizeof(staleText), now + 120);
  snprintf(eventUid, sizeof(eventUid), "GeoChat.%s.%lu", deviceUid, (unsigned long)millis());

  static char cot[1200];
  int len = snprintf(
      cot, sizeof(cot),
      "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>"
      "<event version=\"2.0\" uid=\"%s\" type=\"b-t-f\" time=\"%s\" start=\"%s\" stale=\"%s\" how=\"h-g-i-g-o\">"
      "<point lat=\"%s\" lon=\"%s\" hae=\"%s\" ce=\"9999999.0\" le=\"9999999.0\"/>"
      "<detail>"
      "<__chat parent=\"RootContactGroup\" groupOwner=\"false\" chatroom=\"%s\" id=\"%s\" senderCallsign=\"%s\">"
      "<chatgrp uid0=\"%s\" uid1=\"%s\" id=\"%s\"/>"
      "</__chat>"
      "<link uid=\"%s\" type=\"a-f-G-U-C\" relation=\"p-p\"/>"
      "<remarks source=\"BAO.F.ESP.%s\" to=\"%s\" time=\"%s\">%s</remarks>"
      "</detail></event>",
      eventUid, nowText, nowText, staleText, cfgLat, cfgLon, DEVICE_HAE, peerCallsign, peerUid, cfgCallsign, deviceUid,
      peerUid, peerUid, deviceUid, deviceUid, peerUid, nowText, text);

  if (len <= 0 || len >= (int)sizeof(cot)) {
    Serial.println("聊天回复组包失败");
    return false;
  }
  if (!txUdp.beginPacket(to, CHAT_PORT)) {
    Serial.println("聊天回复发送失败");
    return false;
  }
  txUdp.write((const uint8_t*)cot, len);
  if (!txUdp.endPacket()) {
    Serial.println("聊天回复发送失败");
    return false;
  }
  Serial.print("已回复 ");
  Serial.print(text);
  Serial.print(" -> ");
  printIp(to);
  Serial.println();
  return true;
}

static void formatUptime(char* out, size_t outLen) {
  uint32_t sec = millis() / 1000UL;
  uint32_t days = sec / 86400UL;
  sec %= 86400UL;
  uint32_t hours = sec / 3600UL;
  sec %= 3600UL;
  uint32_t mins = sec / 60UL;
  sec %= 60UL;
  snprintf(out, outLen, "%lu天%lu小时%lu分%lu秒", (unsigned long)days, (unsigned long)hours, (unsigned long)mins,
           (unsigned long)sec);
}

static void buildStatus(char* out, size_t outLen) {
  char uptime[40];
  formatUptime(uptime, sizeof(uptime));
  snprintf(out, outLen, "呼号：%s\n小队：%s\n角色：%s\n位置：%s,%s\n灯：%s\n运行：%s", cfgCallsign, cfgTeam, cfgRole,
           cfgLat, cfgLon, digitalRead(LAMP_PIN) == HIGH ? "开" : "关", uptime);
}

static void rememberPeer(const IPAddress& ip, const char* callsign, const char* uid) {
  lastPeerIp = ip;
  strncpy(lastPeerCallsign, callsign, sizeof(lastPeerCallsign) - 1);
  strncpy(lastPeerUid, uid, sizeof(lastPeerUid) - 1);
  lastPeerCallsign[sizeof(lastPeerCallsign) - 1] = '\0';
  lastPeerUid[sizeof(lastPeerUid) - 1] = '\0';
  hasLastPeer = true;
}

static void replyPrivateChat(const IPAddress& to, const uint8_t* data, int len, int lamp) {
  char peerCallsign[32];
  char peerUid[48];
  if (!extractQuoted(data, len, "senderCallsign", peerCallsign, sizeof(peerCallsign)) ||
      !xmlSafeToken(peerCallsign)) {
    snprintf(peerCallsign, sizeof(peerCallsign), "ATAK");
  }
  if (strcmp(peerCallsign, cfgCallsign) == 0) {
    return;
  }
  if (!extractAndroidUid(data, len, peerUid, sizeof(peerUid))) {
    snprintf(peerUid, sizeof(peerUid), "ATAK");
  }
  rememberPeer(to, peerCallsign, peerUid);

  if (findBytes((const char*)data, len, "状态") != nullptr) {
    char status[220];
    buildStatus(status, sizeof(status));
    sendChatReply(to, status, peerCallsign, peerUid);
    return;
  }

  const char* text = "收到";
  if (lamp > 0) {
    text = "收到，已开灯";
  } else if (lamp < 0) {
    text = "收到，已关灯";
  }
  sendChatReply(to, text, peerCallsign, peerUid);
}

static void sendHello() {
  if (!hasLastPeer || lastPeerIp == IPAddress(0, 0, 0, 0)) {
    Serial.println("还没有私聊对象，未发送你好");
    return;
  }
  sendChatReply(lastPeerIp, "你好", lastPeerCallsign, lastPeerUid);
}

static void serviceButton() {
  static int stable = HIGH;
  static int lastRead = HIGH;
  static uint32_t changedAt = 0;
  int reading = digitalRead(BUTTON_PIN);
  if (reading != lastRead) {
    changedAt = millis();
    lastRead = reading;
  }
  if ((int32_t)(millis() - changedAt) > 40 && reading != stable) {
    stable = reading;
    if (stable == LOW) {
      sendHello();
    }
  }
}

static void receiveOn(WiFiUDP& udp, const char* channel, bool chatPort) {
  int packetSize;
  while ((packetSize = udp.parsePacket()) > 0) {
    IPAddress from = udp.remoteIP();
    uint16_t port = udp.remotePort();
    IPAddress dest = udp.destinationIP();
    const char* kind = channel;
    if (chatPort) {
      kind = (dest == CHAT_MCAST) ? "群聊" : "私聊";
    }

    static uint8_t buf[RX_MAX + 1];
    int toRead = packetSize > RX_MAX ? RX_MAX : packetSize;
    int got = udp.read(buf, toRead);
    while (udp.available()) {
      udp.read();
    }
    if (got < 0) {
      got = 0;
    }
    buf[got] = 0;

    if (from == WiFi.softAPIP()) {
      continue;
    }

    flashLed(120);
    printRawPacket(kind, buf, got, packetSize, from, port, dest);
    if (chatPort && dest != CHAT_MCAST && got > 0) {
      int lamp = applyLampCommand(buf, got);
      replyPrivateChat(from, buf, got, lamp);
    }

    if (got >= 3 && buf[0] == 0xBF && buf[2] == 0xBF && buf[1] == 0 && got > 3) {
      memmove(buf, buf + 3, got - 3);
      got -= 3;
      buf[got] = 0;
      handleText((char*)buf, got, from, port);
      continue;
    }

    if (got >= 3 && buf[0] == 0xBF && buf[2] == 0xBF) {
      printEmbeddedChat(buf + 3, got - 3);
      continue;
    }

    if (buf[0] == '<' || strstr((char*)buf, "<event") != nullptr) {
      handleText((char*)buf, got, from, port);
    }
  }
}

static void trackClients() {
  uint8_t clients = WiFi.softAPgetStationNum();
  if (clients == lastClients) {
    return;
  }
  Serial.printf("热点客户端: %u\n", clients);
  if (clients > lastClients) {
    nextSendMs = millis();
  }
  lastClients = clients;
}

// -------------------- 配置网页 --------------------
static const uint32_t CFG_MAGIC = 0x314B4154UL;
static const int CFG_BYTES = 128;

struct CfgBlob {
  uint32_t magic;
  char callsign[24];
  char team[16];
  char role[24];
  char lat[16];
  char lon[16];
};

static const char* TEAM_VALUES[] = {"White",     "Yellow", "Orange", "Magenta", "Red",     "Maroon",
                                   "Purple",    "Dark Blue", "Blue", "Cyan", "Teal", "Green",
                                   "Dark Green", "Brown"};
static const char* TEAM_LABELS[] = {"白 White",     "黄 Yellow", "橙 Orange", "品红 Magenta", "红 Red",
                                   "栗色 Maroon",   "紫 Purple", "深蓝 Dark Blue", "蓝 Blue", "青 Cyan",
                                   "蓝绿 Teal",     "绿 Green", "深绿 Dark Green", "棕 Brown"};
static const char* ROLE_VALUES[] = {"Team Member", "Team Lead", "HQ", "Sniper", "Medic",
                                   "Forward Observer", "RTO", "K9"};
static const char* ROLE_LABELS[] = {"队员 Team Member", "队长 Team Lead", "指挥 HQ", "狙击 Sniper",
                                   "医疗 Medic", "观察员 Forward Observer", "通信 RTO", "警犬 K9"};
static const int TEAM_COUNT = 14;
static const int ROLE_COUNT = 8;

static ESP8266WebServer webServer(80);

static bool knownOpt(const char* value, const char* const* values, int count) {
  for (int i = 0; i < count; i++) {
    if (strcmp(value, values[i]) == 0) {
      return true;
    }
  }
  return false;
}

static bool validCoord(const char* s, double minV, double maxV) {
  if (s == nullptr || s[0] == '\0' || strlen(s) > 15) {
    return false;
  }
  bool dot = false;
  bool digit = false;
  for (size_t i = 0; s[i] != '\0'; i++) {
    char c = s[i];
    if (i == 0 && (c == '-' || c == '+')) {
      continue;
    }
    if (c == '.') {
      if (dot) {
        return false;
      }
      dot = true;
      continue;
    }
    if (c >= '0' && c <= '9') {
      digit = true;
      continue;
    }
    return false;
  }
  if (!digit) {
    return false;
  }
  double value = atof(s);
  return value >= minV && value <= maxV;
}

static bool validCallsign(const char* s) {
  size_t n = strlen(s);
  if (n < 1 || n > 20) {
    return false;
  }
  for (size_t i = 0; i < n;) {
    unsigned char c = (unsigned char)s[i];
    if (c < 0x20 || c == '<' || c == '>' || c == '&' || c == '"' || c == '\'') {
      return false;
    }
    if (c < 0x80) {
      i++;
      continue;
    }
    int need = 0;
    if ((c & 0xE0) == 0xC0) {
      need = 2;
    } else if ((c & 0xF0) == 0xE0) {
      need = 3;
    } else if ((c & 0xF8) == 0xF0) {
      need = 4;
    }
    if (need == 0 || i + (size_t)need > n) {
      return false;
    }
    for (int k = 1; k < need; k++) {
      if (((unsigned char)s[i + k] & 0xC0) != 0x80) {
        return false;
      }
    }
    i += (size_t)need;
  }
  return true;
}

static void loadConfig() {
  EEPROM.begin(CFG_BYTES);
  CfgBlob blob;
  EEPROM.get(0, blob);
  blob.callsign[sizeof(blob.callsign) - 1] = '\0';
  blob.team[sizeof(blob.team) - 1] = '\0';
  blob.role[sizeof(blob.role) - 1] = '\0';
  blob.lat[sizeof(blob.lat) - 1] = '\0';
  blob.lon[sizeof(blob.lon) - 1] = '\0';
  if (blob.magic != CFG_MAGIC || !validCallsign(blob.callsign) ||
      !knownOpt(blob.team, TEAM_VALUES, TEAM_COUNT) || !knownOpt(blob.role, ROLE_VALUES, ROLE_COUNT)) {
    return;
  }
  strncpy(cfgCallsign, blob.callsign, sizeof(cfgCallsign) - 1);
  strncpy(cfgTeam, blob.team, sizeof(cfgTeam) - 1);
  strncpy(cfgRole, blob.role, sizeof(cfgRole) - 1);
  cfgCallsign[sizeof(cfgCallsign) - 1] = '\0';
  cfgTeam[sizeof(cfgTeam) - 1] = '\0';
  cfgRole[sizeof(cfgRole) - 1] = '\0';
  if (validCoord(blob.lat, -90.0, 90.0) && validCoord(blob.lon, -180.0, 180.0)) {
    strncpy(cfgLat, blob.lat, sizeof(cfgLat) - 1);
    strncpy(cfgLon, blob.lon, sizeof(cfgLon) - 1);
    cfgLat[sizeof(cfgLat) - 1] = '\0';
    cfgLon[sizeof(cfgLon) - 1] = '\0';
  }
}

static void saveConfig() {
  CfgBlob blob = {};
  blob.magic = CFG_MAGIC;
  strncpy(blob.callsign, cfgCallsign, sizeof(blob.callsign) - 1);
  strncpy(blob.team, cfgTeam, sizeof(blob.team) - 1);
  strncpy(blob.role, cfgRole, sizeof(blob.role) - 1);
  strncpy(blob.lat, cfgLat, sizeof(blob.lat) - 1);
  strncpy(blob.lon, cfgLon, sizeof(blob.lon) - 1);
  EEPROM.put(0, blob);
  EEPROM.commit();
}

static const char PAGE_HEAD[] PROGMEM = R"html(
<!DOCTYPE html><html lang="zh-CN"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>TAK-Client-UDP-ESP8266</title>
<style>
body{font-family:sans-serif;background:#121417;color:#e8e8e8;margin:0;padding:20px}
main{max-width:440px;margin:0 auto}
label{display:block;margin:14px 0 6px}
input,select,button{width:100%;box-sizing:border-box;font-size:16px;padding:10px;border-radius:8px;border:1px solid #333;background:#1c2128;color:#fff}
button{margin-top:18px;background:#137a5a;border:0}
.ok{color:#9d9}
</style></head><body><main>
<h1>ATAK 身份</h1>
)html";

static const char PAGE_ERR[] PROGMEM =
    "<!DOCTYPE html><html lang=\"zh-CN\"><head><meta charset=\"utf-8\"></head><body>"
    "<p>呼号、小队颜色、角色或经纬度无效。呼号最多 20 字节，纬度 -90 到 90，经度 -180 到 180。</p>"
    "<p><a href=\"/\">返回</a></p></body></html>";

static void sendEscaped(const char* s) {
  char one[2] = {0, 0};
  for (; *s; s++) {
    if (*s == '&') {
      webServer.sendContent("&amp;");
    } else if (*s == '<') {
      webServer.sendContent("&lt;");
    } else if (*s == '"') {
      webServer.sendContent("&quot;");
    } else {
      one[0] = *s;
      webServer.sendContent(one);
    }
  }
}

static void sendSelect(const char* name, const char* current, const char* const* values, const char* const* labels, int count) {
  webServer.sendContent("<select name=\"");
  webServer.sendContent(name);
  webServer.sendContent("\">");
  for (int i = 0; i < count; i++) {
    webServer.sendContent("<option value=\"");
    webServer.sendContent(values[i]);
    if (strcmp(current, values[i]) == 0) {
      webServer.sendContent("\" selected>");
    } else {
      webServer.sendContent("\">");
    }
    webServer.sendContent(labels[i]);
    webServer.sendContent("</option>");
  }
  webServer.sendContent("</select>");
}

static void handleRoot() {
  webServer.setContentLength(CONTENT_LENGTH_UNKNOWN);
  webServer.send(200, "text/html; charset=utf-8", "");
  webServer.sendContent_P(PAGE_HEAD);
  if (webServer.hasArg("saved")) {
    webServer.sendContent_P(PSTR("<p class=\"ok\">已保存。下一次位置广播会使用新的呼号、颜色、角色和坐标。</p>"));
  }
  webServer.sendContent_P(PSTR("<form method=\"POST\" action=\"/save\"><label>呼号</label>"
                               "<input name=\"callsign\" maxlength=\"20\" required value=\""));
  sendEscaped(cfgCallsign);
  webServer.sendContent_P(PSTR("\"><label>小队颜色</label>"));
  sendSelect("team", cfgTeam, TEAM_VALUES, TEAM_LABELS, TEAM_COUNT);
  webServer.sendContent_P(PSTR("<label>角色</label>"));
  sendSelect("role", cfgRole, ROLE_VALUES, ROLE_LABELS, ROLE_COUNT);
  webServer.sendContent_P(PSTR("<label>纬度</label><input name=\"lat\" required value=\""));
  sendEscaped(cfgLat);
  webServer.sendContent_P(PSTR("\"><label>经度</label><input name=\"lon\" required value=\""));
  sendEscaped(cfgLon);
  webServer.sendContent_P(PSTR("\"><button type=\"submit\">保存</button></form></main></body></html>"));
  webServer.sendContent("");
}

static void copyArg(const char* name, char* out, size_t outLen) {
  out[0] = '\0';
  if (!webServer.hasArg(name) || outLen == 0) {
    return;
  }
  String value = webServer.arg(name);
  value.trim();
  strncpy(out, value.c_str(), outLen - 1);
  out[outLen - 1] = '\0';
}

static void handleSave() {
  char callsign[24];
  char team[16];
  char role[24];
  char lat[16];
  char lon[16];
  copyArg("callsign", callsign, sizeof(callsign));
  copyArg("team", team, sizeof(team));
  copyArg("role", role, sizeof(role));
  copyArg("lat", lat, sizeof(lat));
  copyArg("lon", lon, sizeof(lon));
  if (!validCallsign(callsign) || !knownOpt(team, TEAM_VALUES, TEAM_COUNT) || !knownOpt(role, ROLE_VALUES, ROLE_COUNT) ||
      !validCoord(lat, -90.0, 90.0) || !validCoord(lon, -180.0, 180.0)) {
    webServer.send_P(400, PSTR("text/html; charset=utf-8"), PAGE_ERR);
    return;
  }
  strncpy(cfgCallsign, callsign, sizeof(cfgCallsign) - 1);
  strncpy(cfgTeam, team, sizeof(cfgTeam) - 1);
  strncpy(cfgRole, role, sizeof(cfgRole) - 1);
  strncpy(cfgLat, lat, sizeof(cfgLat) - 1);
  strncpy(cfgLon, lon, sizeof(cfgLon) - 1);
  cfgCallsign[sizeof(cfgCallsign) - 1] = '\0';
  cfgTeam[sizeof(cfgTeam) - 1] = '\0';
  cfgRole[sizeof(cfgRole) - 1] = '\0';
  cfgLat[sizeof(cfgLat) - 1] = '\0';
  cfgLon[sizeof(cfgLon) - 1] = '\0';
  saveConfig();
  nextSendMs = millis();
  webServer.sendHeader("Location", "/?saved=1", true);
  webServer.send(303, "text/plain", "");
}

static void startWeb() {
  webServer.on("/", HTTP_GET, handleRoot);
  webServer.on("/save", HTTP_POST, handleSave);
  webServer.begin();
}

// -------------------- Arduino --------------------
void setup() {
  pinMode(LED_BUILTIN, OUTPUT);
  digitalWrite(LED_BUILTIN, HIGH);
  pinMode(LAMP_PIN, OUTPUT);
  digitalWrite(LAMP_PIN, LOW);
  pinMode(BUTTON_PIN, INPUT_PULLUP);

  Serial.begin(115200);
  delay(200);
  Serial.println();
  Serial.println("TAK-Client-UDP-ESP8266");

  snprintf(deviceUid, sizeof(deviceUid), "ESP8266-%08X", ESP.getChipId());
  clockBaseMs = millis();
  loadConfig();

  WiFi.persistent(false);
  WiFi.mode(WIFI_AP);
  WiFi.setSleepMode(WIFI_NONE_SLEEP);
  WiFi.setOutputPower(20.5);
  WiFi.softAPConfig(AP_IP, AP_GATEWAY, AP_MASK);

  bool apOk;
  if (strlen(AP_PASS) >= 8) {
    apOk = WiFi.softAP(AP_SSID, AP_PASS, AP_CHANNEL, false, AP_MAX_CLIENTS);
  } else {
    apOk = WiFi.softAP(AP_SSID, nullptr, AP_CHANNEL, false, AP_MAX_CLIENTS);
  }

  Serial.printf("热点: %s\n", apOk ? "已启动" : "启动失败");
  Serial.printf("SSID: %s\n", AP_SSID);
  if (strlen(AP_PASS) >= 8) {
    Serial.printf("密码: %s\n", AP_PASS);
  } else {
    Serial.println("密码: 无（开放网络）");
  }
  Serial.print("AP IP: ");
  Serial.println(WiFi.softAPIP());
  Serial.printf("呼号: %s\n", cfgCallsign);
  Serial.printf("小队: %s\n", cfgTeam);
  Serial.printf("角色: %s\n", cfgRole);
  Serial.printf("坐标: %s,%s\n", cfgLat, cfgLon);
  Serial.printf("UID: %s\n", deviceUid);
  Serial.println("配置页: http://192.168.4.1");

  delay(100);
  startWeb();
  joinGroups();
  nextJoinMs = millis() + 3000;
  nextSendMs = millis() + 1000;
}

void loop() {
  if ((!saJoined || !chatJoined) && (int32_t)(millis() - nextJoinMs) >= 0) {
    joinGroups();
    nextJoinMs = millis() + 3000;
  }

  if (saJoined) {
    receiveOn(rxUdp, "SA", false);
  }
  if (chatJoined) {
    receiveOn(chatUdp, "聊天", true);
  }
  serviceLed();
  serviceButton();
  trackClients();
  webServer.handleClient();

  if ((int32_t)(millis() - nextSendMs) >= 0) {
    sendSa();
    nextSendMs = millis() + SEND_INTERVAL_MS;
  }
}
