/*
  OLED Sniffer - ESP32-C3
  OLED I2C slave emulator (SSD1306 / SH1106)
  AP + optional STA WiFi, Bulk RAM capture, fast preview
*/

#include <Arduino.h>
#include <Wire.h>
#include <WiFi.h>
#include <ESPmDNS.h>
#include <WebServer.h>
#include <LittleFS.h>

#define ENABLE_MDNS 1

static constexpr int SDA_PIN = 5;
static constexpr int SCL_PIN = 4;
static constexpr int OLED_W = 128;
static constexpr int OLED_H = 64;
static constexpr int FB_SIZE = 1024;
static constexpr size_t I2C_RX_BUFFER = 1100;
static constexpr uint32_t I2C_CLOCK_HZ = 100000;

static constexpr int MAX_FRAMES = 200;
static constexpr int MAX_RAM_SLOTS = 256;

static const char *AP_SSID = "OLED";
static const char *AP_PASS = "oledsniffer";
static const char *HOSTNAME = "oledsniffer";

static constexpr wifi_power_t WIFI_TX_POWER = WIFI_POWER_2dBm;

static constexpr uint32_t CPU_FREQ_MHZ = 80;

static const char *CONFIG_PATH = "/mode.txt";
static const char *ADDR_PATH = "/addr.txt";
static const char *DRV_PATH  = "/drv.txt";
static const char *WIFI_PATH = "/wifi.txt";

WebServer server(80);

// ---------------- Активные настройки ----------------
static uint8_t oledAddr = 0x3C;
static uint8_t driverMode = 0;   // 0=SSD1306, 1=SH1106

// ---------------- WiFi ----------------
static String staSsid = "";
static String staPass = "";
static volatile bool staWasConnected = false;
static bool apEnabled = false;

struct RenderVariant { const char *name; uint8_t layout, lsb, hf, vf, inv; };

static const RenderVariant RENDER_VARIANTS[] = {
  {"page_std",0,0,0,0,0},{"page_lsb",0,1,0,0,0},{"page_inv",0,0,0,0,1},{"page_hv",0,0,1,1,0},
  {"row_std",1,0,0,0,0},{"row_lsb",1,1,0,0,0},{"row_inv",1,0,0,0,1},{"row_hflip",1,0,1,0,0},
  {"row_vflip",1,0,0,1,0},{"row_hv",1,0,1,1,0},{"row_hv_lsb",1,1,1,1,0},{"row_hv_inv",1,0,1,1,1},
  {"col_std",2,0,0,0,0},{"col_lsb",2,1,0,0,0},{"col_inv",2,0,0,0,1},{"col_hflip",2,0,1,0,0},
  {"col_vflip",2,0,0,1,0},{"col_hv",2,0,1,1,0},{"col_hv_lsb",2,1,1,1,0},
};
static constexpr int RENDER_VARIANTS_COUNT =
    sizeof(RENDER_VARIANTS) / sizeof(RENDER_VARIANTS[0]);

static uint8_t activeMode = 13;
static bool gPix[64][128];
uint8_t framebuffer[FB_SIZE] = {};

static uint8_t *ramBuf = nullptr;
static int ramSlots = 0;
static volatile int ramHead = 0;
static volatile bool ramFull = false;

volatile bool captureRunning = false;
volatile uint32_t captureIntervalMs = 500;
uint32_t lastCaptureMs = 0;

volatile bool processing = false;
volatile bool abortProcessing = false;
volatile int processIdx = 0;
volatile int processTotal = 0;

uint32_t capturedCount = 0;

portMUX_TYPE framebufferMux = portMUX_INITIALIZER_UNLOCKED;

uint8_t controlMode = 0x00;
uint8_t addressingMode = 0;
uint8_t col = 0, page = 0;
uint8_t colStart = 0, colEnd = 127;
uint8_t pageStart = 0, pageEnd = 7;
uint8_t currentCommand = 0, commandArgsLeft = 0;
uint32_t frameNumberCounter = 0;

// Кэш для /api/frames и для free heap — не дёргаем ФС и системные
// вызовы на каждый HTTP-запрос.
static String cachedFramesJson;
static uint32_t cachedFramesAt = 0;
static uint32_t cachedFreeHeap = 0;
static uint32_t cachedHeapAt = 0;

// В ISR только читаем Wire и складываем байты в кольцо.
static constexpr uint16_t I2C_RING_SIZE = 2048;      // 2^11
static constexpr uint16_t I2C_RING_MASK = I2C_RING_SIZE - 1;
// младшие 8 бит — байт, бит 8 — начало новой I2C-транзакции
static volatile uint16_t i2cRing[I2C_RING_SIZE];
static volatile uint16_t i2cHead = 0, i2cTail = 0;

// Состояние разбора (аналог локальных переменных старого onI2CReceive)
static bool i2cNeedControl = true;
static bool i2cOneBytePayload = false;
static uint8_t i2cMode = 0;

// ---------------- Настройки ----------------

void loadMode() {
  File f = LittleFS.open(CONFIG_PATH, "r");
  if (!f) return;
  int m = f.parseInt(); f.close();
  if (m >= 0 && m < RENDER_VARIANTS_COUNT) activeMode = (uint8_t)m;
}
void saveMode() {
  File f = LittleFS.open(CONFIG_PATH, "w");
  if (!f) return;
  f.printf("%d\n", (int)activeMode); f.close();
}
void loadAddr() {
  File f = LittleFS.open(ADDR_PATH, "r");
  if (!f) return;
  String s = f.readString(); f.close(); s.trim();
  long v = strtol(s.c_str(), nullptr, 16);
  if (v == 0x3C || v == 0x3D) oledAddr = (uint8_t)v;
}
void saveAddr() {
  File f = LittleFS.open(ADDR_PATH, "w");
  if (!f) return;
  f.printf("%02X\n", (int)oledAddr); f.close();
}
void loadDriver() {
  File f = LittleFS.open(DRV_PATH, "r");
  if (!f) return;
  int v = f.parseInt(); f.close();
  driverMode = (v == 1) ? 1 : 0;
}
void saveDriver() {
  File f = LittleFS.open(DRV_PATH, "w");
  if (!f) return;
  f.printf("%d\n", (int)driverMode); f.close();
}
void loadWifiCreds() {
  File f = LittleFS.open(WIFI_PATH, "r");
  if (!f) return;
  staSsid = f.readStringUntil('\n'); staSsid.trim();
  staPass = f.readStringUntil('\n'); staPass.trim();
  f.close();
}
void saveWifiCreds() {
  File f = LittleFS.open(WIFI_PATH, "w");
  if (!f) return;
  f.print(staSsid); f.print("\n");
  f.print(staPass); f.print("\n");
  f.close();
}
void clearWifiCreds() {
  staSsid = ""; staPass = "";
  LittleFS.remove(WIFI_PATH);
}
String absPath(const String &name) {
  if (name.startsWith("/")) return name;
  return String("/") + name;
}
uint32_t cachedFreeHeapGet() {
  uint32_t now = millis();
  if (now - cachedHeapAt > 500) {
    cachedFreeHeap = (uint32_t)ESP.getFreeHeap();
    cachedHeapAt = now;
  }
  return cachedFreeHeap;
}

// ---------------- I2C ----------------

//ISR теперь крошечный: читаем Wire и пишем в ring buffer.
void onI2CReceive(int len) {
  if (len <= 0) return;
  bool first = true;
  while (Wire.available()) {
    uint8_t b = (uint8_t)Wire.read();
    uint16_t next = (i2cHead + 1) & I2C_RING_MASK;
    if (next != i2cTail) {
      i2cRing[i2cHead] = (uint16_t)b | (first ? 0x100u : 0u);
      i2cHead = next;
    }
    first = false;
  }
}

void restartI2C() {
  Wire.end();
  delay(20);
  Wire.setBufferSize(I2C_RX_BUFFER);
  bool ok = Wire.begin(oledAddr, SDA_PIN, SCL_PIN, I2C_CLOCK_HZ);
  if (ok) {
    Wire.onReceive(onI2CReceive);
    i2cHead = i2cTail = 0;
    i2cNeedControl = true;
    i2cOneBytePayload = false;
    i2cMode = controlMode;
    Serial.printf("[i2c] addr=0x%02X driver=%s\n",
                  oledAddr, driverMode ? "SH1106" : "SSD1306");
  } else {
    Serial.println("[i2c] restart failed");
  }
}

// ---------------- OLED emulation ----------------

uint8_t commandArgCount(uint8_t cmd) {
  switch (cmd) {
    case 0x20: return 1;
    case 0x21: return 2;
    case 0x22: return 2;
    case 0x81: case 0x8D: case 0xA8: case 0xD3:
    case 0xD5: case 0xD9: case 0xDA: case 0xDB: return 1;
    default: return 0;
  }
}
void applyCommand(uint8_t cmd) {
  if (cmd <= 0x0F) { col = (col & 0xF0) | cmd; return; }
  if (cmd >= 0x10 && cmd <= 0x1F) { col = (col & 0x0F) | ((cmd & 0x0F) << 4); return; }
  if (cmd >= 0xB0 && cmd <= 0xB7) { page = cmd & 0x07; return; }
  if (cmd == 0x40) return;
  uint8_t ac = commandArgCount(cmd);
  if (ac > 0) { currentCommand = cmd; commandArgsLeft = ac; }
}
void applyCommandArg(uint8_t v) {
  if (driverMode == 1) {
    if (commandArgsLeft > 0) commandArgsLeft--;
    return;
  }
  switch (currentCommand) {
    case 0x20: addressingMode = v & 0x03; break;
    case 0x21:
      if (addressingMode == 2) addressingMode = 0;
      if (commandArgsLeft == 2) colStart = v & 0x7F;
      else { colEnd = v & 0x7F; col = colStart; }
      break;
    case 0x22:
      if (addressingMode == 2) addressingMode = 0;
      if (commandArgsLeft == 2) pageStart = v & 0x07;
      else { pageEnd = v & 0x07; page = pageStart; }
      break;
    default: break;
  }
  if (commandArgsLeft > 0) commandArgsLeft--;
}

// Горячий путь: без критических секций. На C3 критическая секция
// выключает прерывания, и при плотном I2C-трафике WiFi-стек падает.
// Одиночная запись байта в память атомарна на RISC-V.
void writeDisplayData(uint8_t v) {
  int fbCol = (driverMode == 1) ? ((int)col - 2) : (int)col;
  if (fbCol >= 0 && fbCol < OLED_W && page < 8) {
    framebuffer[page * OLED_W + fbCol] = v;
  }
  if (driverMode == 1) {
    col++;
    if (col > 131) { col = 0; page = (page + 1) & 0x07; }
    return;
  }
  if (addressingMode == 0) {
    col++;
    if (col > colEnd) { col = colStart; page++; if (page > pageEnd) page = pageStart; }
  } else if (addressingMode == 1) {
    page++;
    if (page > pageEnd) { page = pageStart; col++; if (col > colEnd) col = colStart; }
  } else {
    col++; if (col >= OLED_W) col = 0;
  }
}

static void processI2CByte(uint8_t b) {
  if (i2cNeedControl) {
    if ((b & 0x3F) == 0) {
      i2cMode = b & 0x40;
      controlMode = i2cMode;
      i2cOneBytePayload = (b & 0x80) != 0;
      i2cNeedControl = false;
      return;
    }
    i2cNeedControl = false;
  }
  if (i2cMode == 0x40) {
    writeDisplayData(b);
  } else {
    if (commandArgsLeft > 0) applyCommandArg(b);
    else applyCommand(b);
  }
  if (i2cOneBytePayload) {
    i2cNeedControl = true;
    i2cOneBytePayload = false;
  }
}

static void drainI2CRing() {
  int budget = 512;
  while (i2cTail != i2cHead && budget-- > 0) {
    uint16_t v = i2cRing[i2cTail];
    i2cTail = (i2cTail + 1) & I2C_RING_MASK;
    if (v & 0x100) {
      // начало новой транзакции
      i2cNeedControl = true;
      i2cOneBytePayload = false;
      i2cMode = controlMode;
    }
    processI2CByte((uint8_t)(v & 0xFF));
  }
}

// ---------------- PNG ----------------

uint32_t crc32Buffer(const uint8_t *data, size_t length) {
  uint32_t crc = 0xFFFFFFFF;
  for (size_t i = 0; i < length; i++) {
    crc ^= data[i];
    for (int bit = 0; bit < 8; bit++)
      crc = (crc >> 1) ^ (0xEDB88320UL & (-(int32_t)(crc & 1)));
  }
  return ~crc;
}
uint32_t adler32Buffer(const uint8_t *data, size_t length) {
  uint32_t a = 1, b = 0;
  for (size_t i = 0; i < length; i++) { a = (a + data[i]) % 65521; b = (b + a) % 65521; }
  return (b << 16) | a;
}
void write32BE(File &f, uint32_t v) {
  f.write((uint8_t)(v >> 24)); f.write((uint8_t)(v >> 16));
  f.write((uint8_t)(v >> 8)); f.write((uint8_t)v);
}
bool writePNGChunkFile(File &file, const char *type, const uint8_t *data, uint32_t length) {
  write32BE(file, length);
  file.write((const uint8_t *)type, 4);
  if (length > 0) file.write(data, length);
  uint32_t crc = 0xFFFFFFFF;
  const uint8_t *chunks[2] = {(const uint8_t *)type, data};
  size_t lens[2] = {4, length};
  for (int c = 0; c < 2; c++)
    for (size_t i = 0; i < lens[c]; i++) {
      crc ^= chunks[c][i];
      for (int bit = 0; bit < 8; bit++)
        crc = (crc >> 1) ^ (0xEDB88320UL & (-(int32_t)(crc & 1)));
    }
  write32BE(file, ~crc);
  return true;
}

static uint8_t rawBuf[OLED_H * (OLED_W + 1)];
static uint8_t zlibBuf[2 + OLED_H * (OLED_W + 1) + 5 * 4 + 4];

bool savePixPNGToFile(const String &path) {
  const size_t rawLength = OLED_H * (OLED_W + 1);
  for (int y = 0; y < OLED_H; y++) {
    rawBuf[y * (OLED_W + 1)] = 0;
    for (int x = 0; x < OLED_W; x++)
      rawBuf[y * (OLED_W + 1) + 1 + x] = gPix[y][x] ? 0 : 255;
  }
  size_t pos = 0, offset = 0;
  zlibBuf[pos++] = 0x78; zlibBuf[pos++] = 0x01;
  while (offset < rawLength) {
    uint16_t bl = (uint16_t)min((size_t)65535, rawLength - offset);
    bool fin = (offset + bl == rawLength);
    zlibBuf[pos++] = fin ? 0x01 : 0x00;
    zlibBuf[pos++] = bl & 0xFF; zlibBuf[pos++] = bl >> 8;
    uint16_t inv = ~bl;
    zlibBuf[pos++] = inv & 0xFF; zlibBuf[pos++] = inv >> 8;
    memcpy(zlibBuf + pos, rawBuf + offset, bl);
    pos += bl; offset += bl;
  }
  uint32_t ad = adler32Buffer(rawBuf, rawLength);
  zlibBuf[pos++] = ad >> 24; zlibBuf[pos++] = ad >> 16;
  zlibBuf[pos++] = ad >> 8;  zlibBuf[pos++] = ad;

  File file = LittleFS.open(path, "w");
  if (!file) return false;
  const uint8_t sig[8] = {137, 80, 78, 71, 13, 10, 26, 10};
  file.write(sig, 8);
  uint8_t ihdr[13] = {};
  ihdr[3] = OLED_W; ihdr[7] = OLED_H; ihdr[8] = 8; ihdr[9] = 0;
  writePNGChunkFile(file, "IHDR", ihdr, 13);
  writePNGChunkFile(file, "IDAT", zlibBuf, pos);
  writePNGChunkFile(file, "IEND", nullptr, 0);
  file.close();
  return true;
}

void renderFramebuffer(const uint8_t *fb, uint8_t mode) {
  const RenderVariant &v = RENDER_VARIANTS[mode];
  memset(gPix, 0, sizeof(gPix));
  for (int i = 0; i < 1024; i++) {
    uint8_t b = fb[i];
    for (int j = 0; j < 8; j++) {
      int bp = v.lsb ? j : (7 - j);
      bool val = (b >> bp) & 1;
      int x, y;
      if (v.layout == 0) { x = i % 128; y = (i / 128) * 8 + j; }
      else if (v.layout == 1) { x = (i % 16) * 8 + j; y = i / 16; }
      else { x = i / 8; y = (i % 8) * 8 + j; }
      if (v.hf) x = 127 - x;
      if (v.vf) y = 63 - y;
      if (v.inv) val = !val;
      if (x >= 0 && x < 128 && y >= 0 && y < 64) gPix[y][x] = val;
    }
  }
}

String frameFilename(uint32_t n) {
  char b[32]; snprintf(b, sizeof(b), "/frame_%06lu.png", (unsigned long)n);
  return String(b);
}
void findLastFrameNumber() {
  File root = LittleFS.open("/");
  if (!root) return;
  File file = root.openNextFile();
  while (file) {
    String name = file.name();
    int marker = name.lastIndexOf("frame_");
    if (marker >= 0 && name.endsWith(".png")) {
      String number = name.substring(marker + 6);
      number.replace(".png", "");
      uint32_t n = (uint32_t)number.toInt();
      if (n > frameNumberCounter) frameNumberCounter = n;
    }
    file = root.openNextFile();
  }
  root.close();
}
void pruneOldFrames(uint32_t newest) {
  if (newest <= (uint32_t)MAX_FRAMES) return;
  LittleFS.remove(frameFilename(newest - MAX_FRAMES));
}
String escapeJSON(const String &input) {
  String output;
  for (size_t i = 0; i < input.length(); i++) {
    char c = input[i];
    if (c == '"' || c == '\\') output += '\\';
    if ((uint8_t)c >= 32) output += c;
  }
  return output;
}

void allocateRamBufferIfNeeded() {
  if (ramBuf != nullptr) return;
  size_t freeHeap = ESP.getFreeHeap();
  int budgetKb = (int)((freeHeap > 100000) ? (freeHeap - 60000) / 1024 : 0);
  if (budgetKb > MAX_RAM_SLOTS) budgetKb = MAX_RAM_SLOTS;
  if (budgetKb < 4) budgetKb = 4;
  for (int want = budgetKb; want >= 4; want -= 4) {
    ramBuf = (uint8_t *)malloc((size_t)want * FB_SIZE);
    if (ramBuf) { ramSlots = want; return; }
  }
  ramSlots = 0;
}

void startProcessing() {
  if (processing) return;
  if (ramHead <= 0) return;
  processing = true;
  abortProcessing = false;
  processIdx = 0;
  processTotal = ramHead;
  Serial.printf("[process] start, %d frames\n", ramHead);
}

// ---------------- WiFi ----------------

void updateApState() {
  static uint32_t staDownSince = 0;
  bool staUp = (WiFi.status() == WL_CONNECTED);

  if (staUp) {
    staDownSince = 0;
    if (apEnabled) {
      WiFi.softAPdisconnect(true);
      apEnabled = false;
      WiFi.mode(WIFI_STA);
      WiFi.setSleep(true);
      if (WiFi.localIP() == IPAddress(0, 0, 0, 0) && staSsid.length() > 0) {
        WiFi.disconnect(false, false);
        WiFi.begin(staSsid.c_str(), staPass.c_str());
        Serial.println("[wifi] STA re-init after mode switch");
      }
      Serial.println("[wifi] AP disabled, mode=STA (sleep ON)");
    }
    return;
  }

  if (staDownSince == 0) staDownSince = millis();
  if (!apEnabled && (millis() - staDownSince > 10000)) {
    WiFi.setSleep(false);
    WiFi.mode(WIFI_AP_STA);
    WiFi.setSleep(false);
    bool ok = WiFi.softAP(AP_SSID, AP_PASS);
    apEnabled = ok;
    if (ok) {
      Serial.printf("[wifi] AP enabled (STA down >10s), IP=%s\n",
                    WiFi.softAPIP().toString().c_str());
    } else {
      Serial.println("[wifi] softAP re-enable FAILED");
    }
  }
}

void setupWiFi() {
  WiFi.persistent(false);
  WiFi.mode(WIFI_AP_STA);
  WiFi.setSleep(false);

  WiFi.setTxPower(WIFI_TX_POWER);

  WiFi.setHostname(HOSTNAME);

  bool ok = WiFi.softAP(AP_SSID, AP_PASS);
  apEnabled = ok;
  if (ok) {
    Serial.print("[wifi] AP SSID="); Serial.print(AP_SSID);
    Serial.print(" IP="); Serial.println(WiFi.softAPIP());
  } else {
    Serial.println("[wifi] softAP FAILED — check AP_SSID/AP_PASS");
  }

  if (staSsid.length() > 0) {
    Serial.printf("[wifi] starting STA to %s\n", staSsid.c_str());
    WiFi.begin(staSsid.c_str(), staPass.c_str());
  } else {
    Serial.println("[wifi] no STA credentials, AP-only");
  }

#if ENABLE_MDNS
  if (MDNS.begin(HOSTNAME)) Serial.println("[wifi] mDNS: http://oledsniffer.local/");
#endif
}

// ---------------- Handlers ----------------

void handleCaptureStart() {
  uint32_t ms = 500;
  if (server.hasArg("ms")) {
    long v = server.arg("ms").toInt();
    if (v < 30) v = 30;
    if (v > 3600000) v = 3600000;
    ms = (uint32_t)v;
  }
  if (processing) { server.send(409, "text/plain", "processing"); return; }
  allocateRamBufferIfNeeded();
  if (ramSlots <= 0) { server.send(500, "text/plain", "no ram"); return; }
  ramHead = 0; ramFull = false;
  captureIntervalMs = ms;
  captureRunning = true;
  lastCaptureMs = millis() - ms;
  Serial.printf("[capture] start ms=%lu slots=%d\n", (unsigned long)ms, ramSlots);
  server.sendHeader("Location", "/"); server.send(302, "text/plain", "");
}
void handleCaptureStop() {
  if (captureRunning) {
    captureRunning = false;
    if (ramHead > 0) startProcessing();
  } else if (processing) {
    abortProcessing = true;
  }
  server.sendHeader("Location", "/"); server.send(302, "text/plain", "");
}

void handleSetMode() {
  if (server.hasArg("m")) {
    int m = server.arg("m").toInt();
    if (m >= 0 && m < RENDER_VARIANTS_COUNT) { activeMode = (uint8_t)m; saveMode(); }
  }
  String back = server.hasArg("back") ? server.arg("back") : "/";
  server.sendHeader("Location", back); server.send(302, "text/plain", "");
}
void handleToggleAddr() {
  oledAddr = (oledAddr == 0x3C) ? 0x3D : 0x3C;
  saveAddr();
  restartI2C();
  Serial.printf("[addr] now 0x%02X\n", oledAddr);
  String back = server.hasArg("back") ? server.arg("back") : "/";
  server.sendHeader("Location", back); server.send(302, "text/plain", "");
}
void handleToggleDriver() {
  driverMode = driverMode ? 0 : 1;
  saveDriver();
  portENTER_CRITICAL(&framebufferMux);
  memset(framebuffer, 0, FB_SIZE);
  portEXIT_CRITICAL(&framebufferMux);
  addressingMode = (driverMode == 1) ? 2 : 0;
  col = 0; page = 0;
  Serial.printf("[driver] now %s\n", driverMode ? "SH1106" : "SSD1306");
  String back = server.hasArg("back") ? server.arg("back") : "/";
  server.sendHeader("Location", back); server.send(302, "text/plain", "");
}

// WiFi endpoints
void handleWifiSet() {
  String ssid = server.hasArg("ssid") ? server.arg("ssid") : "";
  String pass = server.hasArg("pass") ? server.arg("pass") : "";
  ssid.trim();
  if (ssid.length() == 0) {
    server.sendHeader("Location", "/"); server.send(302, "text/plain", "");
    return;
  }
  staSsid = ssid;
  staPass = pass;
  saveWifiCreds();
  Serial.printf("[wifi] saved STA %s, connecting in background\n", ssid.c_str());
  WiFi.begin(staSsid.c_str(), staPass.c_str());
  server.sendHeader("Location", "/"); server.send(302, "text/plain", "");
}
void handleWifiForget() {
  clearWifiCreds();
  WiFi.disconnect(false, true);
  staWasConnected = false;
  if (!apEnabled) {
    WiFi.setSleep(false);
    WiFi.mode(WIFI_AP_STA);
    WiFi.setSleep(false);
    apEnabled = WiFi.softAP(AP_SSID, AP_PASS);
    if (apEnabled) {
      Serial.printf("[wifi] AP re-enabled, IP=%s\n", WiFi.softAPIP().toString().c_str());
    } else {
      Serial.println("[wifi] softAP re-enable FAILED");
    }
  }
  Serial.println("[wifi] STA credentials removed");
  server.sendHeader("Location", "/"); server.send(302, "text/plain", "");
}
void handleWifiReconnect() {
  if (staSsid.length() > 0) {
    WiFi.disconnect(false, false);
    WiFi.begin(staSsid.c_str(), staPass.c_str());
    Serial.println("[wifi] reconnect requested");
  }
  server.sendHeader("Location", "/"); server.send(302, "text/plain", "");
}
void handleApiWifi() {
  bool staUp = (WiFi.status() == WL_CONNECTED);
  String json = "{";
  json += "\"ap_ssid\":\"" + String(AP_SSID) + "\"";
  json += ",\"ap_enabled\":" + String(apEnabled ? "true" : "false");
  json += ",\"ap_ip\":\"" + (apEnabled ? WiFi.softAPIP().toString() : String("")) + "\"";
  json += ",\"ap_clients\":" + String(apEnabled ? (int)WiFi.softAPgetStationNum() : 0);
  json += ",\"sta_ssid\":\"" + escapeJSON(staSsid) + "\"";
  json += ",\"sta_configured\":" + String(staSsid.length() > 0 ? "true" : "false");
  json += ",\"sta_connected\":" + String(staUp ? "true" : "false");
  json += ",\"sta_ip\":\"" + (staUp ? WiFi.localIP().toString() : String("")) + "\"";
  json += ",\"sta_rssi\":" + String(staUp ? WiFi.RSSI() : 0);
  json += "}";
  WiFiClient c = server.client(); c.setNoDelay(true);
  server.sendHeader("Connection", "keep-alive");
  server.send(200, "application/json", json);
}

void handleApiMode() {
  String json = "{\"mode\":" + String((int)activeMode);
  json += ",\"count\":" + String((int)RENDER_VARIANTS_COUNT);
  json += ",\"name\":\"" + String(RENDER_VARIANTS[activeMode].name) + "\"";
  json += ",\"addr\":\"" + String(oledAddr == 0x3C ? "0x3C" : "0x3D") + "\"";
  json += ",\"driver\":\"" + String(driverMode ? "SH1106" : "SSD1306") + "\"";
  json += "}";
  server.send(200, "application/json", json);
}

void handlePreviewBin() {
  static uint8_t snap[FB_SIZE];
  portENTER_CRITICAL(&framebufferMux);
  memcpy(snap, framebuffer, FB_SIZE);
  portEXIT_CRITICAL(&framebufferMux);
  WiFiClient c = server.client(); c.setNoDelay(true);
  server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
  server.sendHeader("Connection", "keep-alive");
  server.setContentLength(FB_SIZE);
  server.send(200, "application/octet-stream", "");
  server.sendContent((const char *)snap, FB_SIZE);
}

void handleClear() {
  String what = server.hasArg("what") ? server.arg("what") : "all";

  File root = LittleFS.open("/");
  int removed = 0;
  if (root) {
    File f = root.openNextFile();
    while (f) {
      String an = absPath(f.name());
      f.close();
      if (an != CONFIG_PATH && an != ADDR_PATH && an != DRV_PATH && an != WIFI_PATH) {
        bool del = false;
        if (what == "all") del = true;
        else if (what == "renders" && an.indexOf("/r_") >= 0) del = true;
        if (del) { LittleFS.remove(an); removed++; }
      }
      f = root.openNextFile();
    }
    root.close();
  }
  if (what == "all") { frameNumberCounter = 0; capturedCount = 0; }
  cachedFramesJson = "";
  cachedFramesAt = 0;
  Serial.printf("[clear] %s removed=%d\n", what.c_str(), removed);
  server.sendHeader("Location", "/"); server.send(302, "text/plain", "");
}

struct ZipEntry { String name; uint32_t crc; uint32_t size; uint32_t offset; };
static void putLE16(uint8_t *&p, uint16_t v) { *p++ = v & 0xff; *p++ = v >> 8; }
static void putLE32(uint8_t *&p, uint32_t v) {
  *p++ = v & 0xff; *p++ = (v >> 8) & 0xff; *p++ = (v >> 16) & 0xff; *p++ = (v >> 24) & 0xff;
}

void handleZip() {
  const int MAXE = 260;
  ZipEntry *entries = new ZipEntry[MAXE];
  if (!entries) { server.send(500, "text/plain", "oom"); return; }
  int count = 0;
  File root = LittleFS.open("/");
  if (root) {
    File f = root.openNextFile();
    while (f && count < MAXE) {
      String name = f.name();
      if (name.endsWith(".png") || name.endsWith(".txt")) {
        entries[count].name = absPath(name);
        entries[count].crc = 0; entries[count].size = 0; entries[count].offset = 0;
        count++;
      }
      f = root.openNextFile();
    }
    root.close();
  }
  for (int i = 0; i < count; i++) {
    File ff = LittleFS.open(entries[i].name, "r");
    if (!ff) continue;
    size_t sz = ff.size();
    uint8_t *buf = (uint8_t *)malloc(sz);
    if (!buf) { ff.close(); continue; }
    ff.read(buf, sz); ff.close();
    entries[i].crc = crc32Buffer(buf, sz);
    entries[i].size = sz;
    free(buf);
    yield();
  }
  server.setContentLength(CONTENT_LENGTH_UNKNOWN);
  server.sendHeader("Content-Disposition", "attachment; filename=\"oled_capture.zip\"");
  server.send(200, "application/zip", "");
  uint32_t offset = 0;
  uint8_t buf[256];
  for (int i = 0; i < count; i++) {
    String nm = entries[i].name;
    if (nm.startsWith("/")) nm.remove(0, 1);
    uint16_t nlen = nm.length();
    entries[i].offset = offset;
    uint8_t lh[30]; uint8_t *p = lh;
    putLE32(p, 0x04034b50); putLE16(p, 20); putLE16(p, 0); putLE16(p, 0);
    putLE16(p, 0); putLE16(p, 0);
    putLE32(p, entries[i].crc);
    putLE32(p, entries[i].size); putLE32(p, entries[i].size);
    putLE16(p, nlen); putLE16(p, 0);
    server.sendContent((const char *)lh, 30);
    server.sendContent(nm);
    offset += 30 + nlen;
    File ff = LittleFS.open(entries[i].name, "r");
    if (ff) {
      while (ff.available()) {
        size_t n = ff.read(buf, sizeof(buf));
        if (!n) break;
        server.sendContent((const char *)buf, n);
        offset += n; yield();
      }
      ff.close();
    }
  }
  uint32_t cdStart = offset, cdSize = 0;
  for (int i = 0; i < count; i++) {
    String nm = entries[i].name;
    if (nm.startsWith("/")) nm.remove(0, 1);
    uint16_t nlen = nm.length();
    uint8_t ch[46]; uint8_t *p = ch;
    putLE32(p, 0x02014b50); putLE16(p, 20); putLE16(p, 20);
    putLE16(p, 0); putLE16(p, 0); putLE16(p, 0); putLE16(p, 0);
    putLE32(p, entries[i].crc);
    putLE32(p, entries[i].size); putLE32(p, entries[i].size);
    putLE16(p, nlen); putLE16(p, 0); putLE16(p, 0); putLE16(p, 0);
    putLE16(p, 0); putLE32(p, 0);
    putLE32(p, entries[i].offset);
    server.sendContent((const char *)ch, 46);
    server.sendContent(nm);
    cdSize += 46 + nlen;
    yield();
  }
  {
    uint8_t eocd[22]; uint8_t *p = eocd;
    putLE32(p, 0x06054b50); putLE16(p, 0); putLE16(p, 0);
    putLE16(p, (uint16_t)count); putLE16(p, (uint16_t)count);
    putLE32(p, cdSize); putLE32(p, cdStart); putLE16(p, 0);
    server.sendContent((const char *)eocd, 22);
  }
  server.sendContent("");
  delete[] entries;
}

void handleFiles() {
  File root = LittleFS.open("/");
  if (!root) { server.send(500, "text/plain", "no fs"); return; }
  server.setContentLength(CONTENT_LENGTH_UNKNOWN);
  server.send(200, "text/plain; charset=utf-8", "");
  char line[256];
  int p = snprintf(line, sizeof(line), "LittleFS files:\n");
  server.sendContent(line, p);
  File file = root.openNextFile();
  while (file) {
    String an = absPath(file.name());
    p = snprintf(line, sizeof(line), "  %-32s  %u bytes\n", an.c_str(), (unsigned)file.size());
    server.sendContent(line, p);
    file = root.openNextFile();
  }
  root.close();
  p = snprintf(line, sizeof(line), "\nUsed: %u / %u\n",
               (unsigned)LittleFS.usedBytes(), (unsigned)LittleFS.totalBytes());
  server.sendContent(line, p);
  server.sendContent("");
}

void handleRenders() {
  if (server.hasArg("m")) {
    int m = server.arg("m").toInt();
    if (m >= 0 && m < RENDER_VARIANTS_COUNT) { activeMode = (uint8_t)m; saveMode(); }
    if (server.hasArg("back")) {
      String back = server.arg("back");
      server.sendHeader("Location", back);
      server.send(302, "text/plain", "");
      return;
    }
  }
  server.setContentLength(CONTENT_LENGTH_UNKNOWN);
  server.send(200, "text/html; charset=utf-8", "");
  server.sendContent("<html><head><meta charset=\"utf-8\"><title>renders</title>");
  server.sendContent("<style>body{background:#111;color:#eee;font:13px system-ui;margin:0;padding:14px}"
                     "h2{margin:8px 0}.g{display:grid;grid-template-columns:repeat(auto-fill,minmax(300px,1fr));gap:10px;margin-top:12px}"
                     ".c{background:#1a1f2a;padding:8px;border-radius:8px;border:2px solid transparent}"
                     ".c.active{border-color:#1e6fd9}"
                     "img{width:100%;image-rendering:pixelated;background:#fff;border-radius:4px;aspect-ratio:2/1;object-fit:contain}"
                     "small{color:#9aa6ba}a{color:#9ed0ff;text-decoration:none}"
                     ".note{color:#9aa6ba;margin:6px 0 12px}</style></head><body>");
  server.sendContent("<h2>Выбор режима захвата</h2>");
  server.sendContent("<p class=\"note\">Кликни по правильно отрендеренной картинке. Текущий режим: <b>");
  server.sendContent(RENDER_VARIANTS[activeMode].name);
  server.sendContent("</b>. <a href=\"/\">   Ну или нажми сюда если хочешь вернуться на главную</a></p><div class=\"g\">");
  static uint8_t snap[FB_SIZE];
  portENTER_CRITICAL(&framebufferMux);
  memcpy(snap, framebuffer, FB_SIZE);
  portEXIT_CRITICAL(&framebufferMux);
  for (int k = 0; k < RENDER_VARIANTS_COUNT; k++) {
    renderFramebuffer(snap, (uint8_t)k);
    String fn = String("/r_") + RENDER_VARIANTS[k].name + ".png";
    savePixPNGToFile(fn);
    String card = "<div class=\"c";
    if (k == activeMode) card += " active";
    card += "\"><a href=\"/renders?m="; card += String(k);
    card += "&back=/\"><img src=\""; card += fn;
    card += "?t="; card += String(millis());
    card += "\" loading=\"lazy\"></a><div><small>";
    card += String(k); card += " - "; card += RENDER_VARIANTS[k].name;
    card += "</small></div></div>";
    server.sendContent(card);
    yield();
  }
  server.sendContent("</div></body></html>");
  server.sendContent("");
}

void handleFrames() {
  uint32_t now = millis();
  if (cachedFramesJson.length() > 0 && now - cachedFramesAt < 3000) {
    WiFiClient c = server.client(); c.setNoDelay(true);
    server.sendHeader("Connection", "keep-alive");
    server.send(200, "application/json", cachedFramesJson);
    return;
  }

  String json;
  json.reserve(2048);
  json = "{\"mode\":" + String((int)activeMode);
  json += ",\"addr\":\"" + String(oledAddr == 0x3C ? "0x3C" : "0x3D") + "\"";
  json += ",\"driver\":\"" + String(driverMode ? "SH1106" : "SSD1306") + "\"";
  json += ",\"capture_running\":" + String(captureRunning ? "true" : "false");
  json += ",\"interval_ms\":" + String((unsigned long)captureIntervalMs);
  json += ",\"captured\":" + String((unsigned long)capturedCount);
  json += ",\"ram_slots\":" + String(ramSlots);
  json += ",\"ram_used\":" + String((int)ramHead);
  json += ",\"ram_full\":" + String(ramFull ? "true" : "false");
  json += ",\"processing\":" + String(processing ? "true" : "false");
  json += ",\"process_idx\":" + String((int)processIdx);
  json += ",\"process_total\":" + String((int)processTotal);
  json += ",\"free_heap\":" + String(cachedFreeHeapGet());
  json += ",\"free\":" + String((unsigned)(
      LittleFS.totalBytes() >= LittleFS.usedBytes()
        ? LittleFS.totalBytes() - LittleFS.usedBytes() : 0));
  json += ",\"frames\":[";
  bool first = true;
  File root = LittleFS.open("/");
  File file = root.openNextFile();
  while (file) {
    String name = file.name();
    if (name.endsWith(".png") && name.indexOf("frame_") >= 0) {
      String bn = absPath(name);
      if (bn.startsWith("/")) bn.remove(0, 1);
      if (!first) json += ",";
      json += "{\"name\":\"" + escapeJSON(bn) + "\",\"url\":\"/" + bn + "\"}";
      first = false;
    }
    file = root.openNextFile();
  }
  root.close();
  json += "]}";

  cachedFramesJson = json;
  cachedFramesAt = now;

  WiFiClient c = server.client(); c.setNoDelay(true);
  server.sendHeader("Connection", "keep-alive");
  server.send(200, "application/json", json);
}

void handleIndex() {
  WiFiClient c = server.client();
  c.setNoDelay(true);

  String html;
  html.reserve(11500);
  html += F(
    "<!doctype html><html lang=\"ru\"><head>"
    "<meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">"
    "<title>OLED Sniffer</title>"
    "<style>"
    ":root{color-scheme:dark}*{box-sizing:border-box}"
    "body{margin:0;background:#0b0d12;color:#e7eaf0;font:14px system-ui,sans-serif}"
    "a{color:#9ed0ff;text-decoration:none}a:hover{text-decoration:underline}"
    ".wrap{max-width:1200px;margin:auto;padding:16px}"
    ".toprow{display:flex;flex-direction:column;align-items:stretch;"
    "gap:14px;margin-bottom:14px}"
    ".toprow > .box{display:flex;flex-direction:column}"
    ".box.preview-box{width:100%;justify-content:center;gap:8px}"
    ".box.settings-box{width:100%}"
    ".pill{display:inline-block;background:#151c28;border:1px solid #293244;padding:5px 9px;border-radius:9px;margin:0 5px 5px 0;font-size:12px}"
    ".tok{cursor:pointer;transition:background .15s,border-color .15s}"
    ".tok:hover{background:#222f46;border-color:#3a557f;text-decoration:none}"
    ".box{background:#121722;border:1px solid #293244;border-radius:10px;padding:10px}"
    ".title{font-size:15px;font-weight:600;color:#e7eaf0;margin:0 0 10px 0;letter-spacing:.2px}"
    "canvas#cv{display:block;width:100%;aspect-ratio:2/1;"
    "image-rendering:pixelated;background:#fff;border-radius:6px}"
    ".meta{margin-top:6px;font-size:12px;color:#9aa6ba;display:flex;justify-content:space-between;gap:8px}"
    ".meta b{color:#e7eaf0}"
    ".row{display:flex;gap:8px;flex-wrap:wrap;align-items:center;margin-top:10px}"
    ".actions-row{margin-top:26px}"
    ".row.no-mt{margin-top:0}"
    "input[type=number],input[type=text],input[type=password]{background:#0b0d12;color:#e7eaf0;border:1px solid #293244;border-radius:6px;padding:6px 8px;font:14px system-ui}"
    "input[type=number]{width:70px}"
    "input[type=text]{width:140px}input[type=password]{width:140px}"
    ".btn{background:#1e6fd9;color:#fff;border:0;border-radius:7px;padding:7px 14px;font:14px system-ui;cursor:pointer;text-decoration:none;display:inline-block}"
    ".btn:hover{background:#2a80ea;text-decoration:none}"
    ".btn.stop{background:#7a1f1f}.btn.stop:hover{background:#9c2a2a}"
    ".btn.gray{background:#2a3346}.btn.gray:hover{background:#394663}"
    ".btn.tiny{padding:4px 9px;font-size:12px}"
    ".status{display:inline-flex;gap:6px;align-items:center;font-size:13px;padding:5px 9px;border-radius:7px;background:#151c28;border:1px solid #293244}"
    ".dot{width:9px;height:9px;border-radius:50%;background:#555}"
    ".dot.on{background:#23c957;box-shadow:0 0 6px #23c957}"
    ".dot.proc{background:#f5a623;box-shadow:0 0 6px #f5a623}"
    ".bar{height:6px;border-radius:3px;background:#1a2230;overflow:hidden;margin-top:6px;display:none}"
    ".bar > i{display:block;height:100%;background:#1e6fd9;width:0;transition:width .2s}"
    ".bar.show{display:block}"
    ".grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(170px,1fr));gap:10px;margin-top:6px}"
    ".card{background:#121722;border:1px solid #293244;border-radius:10px;padding:8px;font-size:11px}"
    ".card img{display:block;width:100%;image-rendering:pixelated;background:#fff;border-radius:5px;aspect-ratio:2/1;object-fit:contain}"
    ".card .cr{display:flex;justify-content:space-between;margin-top:5px;gap:5px}"
    "details.wifi{background:#0f1420;border:1px solid #293244;border-radius:9px;padding:8px 10px;margin-bottom:12px}"
    "details.wifi summary{cursor:pointer;color:#9ed0ff;font-size:13px;outline:none}"
    "details.wifi[open] summary{margin-bottom:8px}"
    ".spacer{flex:1}"
    "small{color:#98a3b7}"
    "</style></head><body>"
    "<div class=\"wrap\">"
    "<div class=\"toprow\">"

    "<div class=\"box preview-box\">"
    "<canvas id=\"cv\" width=\"128\" height=\"64\"></canvas>"
    "<div class=\"meta\">"
    "<span>Экран · режим: <b id=\"mn\">-</b> · <a href=\"/renders\">Выбрать режим</a></span>"
    "<span>FPS: <b id=\"fps\">-</b></span>"
    "</div>"
    "</div>"

    "<div class=\"box settings-box\">"

    "<div class=\"title\">OLED Sniffer — I2C Display Emulator</div>"

    "<details class=\"wifi\"><summary>WiFi · AP: <b id=\"apssid\">-</b> · STA: <b id=\"stast\">-</b></summary>"
    "<div><small>Устройство поднимает свою точку <b>OLED</b> (пароль <b>oledsniffer</b>, IP <b>192.168.4.1</b>). "
    "При подключении к домашней сети встроенная точка автоматически отключается, "
    "а IP устройства появится в вашем роутере. Если домашняя сеть отвалится больше чем на 10 с — "
    "точка вернётся, чтобы был доступ для отладки.</small></div>"
    "<form class=\"row\" action=\"/wifi/set\" method=\"get\">"
    "<input type=\"text\" name=\"ssid\" placeholder=\"SSID\" maxlength=\"32\">"
    "<input type=\"password\" name=\"pass\" placeholder=\"пароль\" maxlength=\"64\">"
    "<button class=\"btn\" type=\"submit\">Подключить</button>"
    "<a class=\"btn gray tiny\" href=\"/wifi/reconnect\">Переподключить</a>"
    "<a class=\"btn gray tiny\" href=\"/wifi/forget\" onclick=\"return confirm('Забыть домашнюю сеть?')\">Забыть</a>"
    "</form>"
    "<div class=\"row\"><small>AP: <b id=\"apip\">-</b> · клиентов: <b id=\"apcl\">-</b> · STA: <b id=\"staip\">-</b> · RSSI: <b id=\"rssi\">-</b></small></div>"
    "</details>"

    "<div>"
    "<span class=\"pill\">PNG: <b id=\"c\">-</b></span>"
    "<span class=\"pill\">Сохранено: <b id=\"cap\">-</b></span>"
    "<span class=\"pill\">RAM: <b id=\"ram\">-</b></span>"
    "<span class=\"pill\">Heap: <b id=\"heap\">-</b></span>"
    "<span class=\"pill\">FS: <b id=\"f\">-</b></span>"
    "<a class=\"pill tok\" href=\"/toggle-addr\" title=\"Клик - сменить I²C адрес\">I²C: <b id=\"addr\">-</b></a>"
    "<a class=\"pill tok\" href=\"/toggle-driver\" title=\"Клик - сменить драйвер\"><b id=\"drv\">-</b></a>"
    "</div>"

    "<div class=\"row\">"
    "<span class=\"status\"><span class=\"dot\" id=\"dot\"></span><span id=\"stt\">остановлен</span></span>"
    "<label>Интервал, мс: <input type=\"number\" id=\"ms\" value=\"500\" min=\"200\" max=\"600000\" step=\"200\"></label>"
    "<button class=\"btn\" id=\"bstart\">Захват</button>"
    "<button class=\"btn stop\" id=\"bstop\">Стоп</button>"
    "</div>"
    "<div class=\"bar\" id=\"pbar\"><i id=\"pfill\"></i></div>"

    "<div class=\"row actions-row\">"
    "<a class=\"btn gray\" href=\"/zip\">Скачать всё (ZIP)</a>"
    "<button class=\"btn gray\" onclick=\"clr('all')\">Очистить всё</button>"
    "</div>"

    "</div>"
    "</div>"
    "<div id=\"g\" class=\"grid\"></div>"
    "</div>"
    "<script>"
    "const MODES=["
  );
  for (int i = 0; i < RENDER_VARIANTS_COUNT; i++) {
    char tmp[80];
    snprintf(tmp, sizeof(tmp), "%s{layout:%u,lsb:%u,hf:%u,vf:%u,inv:%u}",
             i ? "," : "",
             RENDER_VARIANTS[i].layout, RENDER_VARIANTS[i].lsb,
             RENDER_VARIANTS[i].hf, RENDER_VARIANTS[i].vf,
             RENDER_VARIANTS[i].inv);
    html += tmp;
  }
  html += F(
    "];"
    "let currentMode=13, previewCnt=0, lastFpsT=0;"
    "const cv=document.getElementById('cv');const ctx=cv.getContext('2d');"
    "const imgData=ctx.createImageData(128,64);const px=imgData.data;"
    "for(let i=0;i<128*64;i++)px[i*4+3]=255;"
    "function drawPreview(fb){"
    " const V=MODES[currentMode];"
    " for(let i=0;i<1024;i++){"
    "  const b=fb[i];"
    "  for(let j=0;j<8;j++){"
    "   const bp=V.lsb?j:(7-j);let val=(b>>bp)&1;let x,y;"
    "   if(V.layout===0){x=i%128;y=((i/128)|0)*8+j;}"
    "   else if(V.layout===1){x=(i%16)*8+j;y=(i/16)|0;}"
    "   else{x=(i/8)|0;y=(i%8)*8+j;}"
    "   if(V.hf)x=127-x;if(V.vf)y=63-y;if(V.inv)val=!val;"
    "   if(x<0||x>=128||y<0||y>=64)continue;"
    "   const p=(y*128+x)*4;const c=val?0:255;"
    "   px[p]=c;px[p+1]=c;px[p+2]=c;"
    "  }}ctx.putImageData(imgData,0,0);}"
    "async function previewLoop(){"
    " while(true){"
    "  const t0=performance.now();"
    "  try{"
    "   const r=await fetch('/preview.bin',{cache:'no-store'});"
    "   if(r.ok){"
    "    const b=new Uint8Array(await r.arrayBuffer());"
    "    drawPreview(b);previewCnt++;"
    "    const now=performance.now();"
    "    if(now-lastFpsT>=1000){document.getElementById('fps').textContent=previewCnt;previewCnt=0;lastFpsT=now;}"
    "   }"
    "  }catch(e){}"
    "  const dt=performance.now()-t0;"
    "  const wait=10-dt;"
    "  if(wait>0)await new Promise(r=>setTimeout(r,wait));"
    " }"
    "}"
    "function clr(what){if(!confirm('Удалить: '+what+'?'))return;location.href='/clear?what='+what;}"
    "function card(f){const c=document.createElement('div');c.className='card';c.dataset.name=f.name;"
    " const i=document.createElement('img');i.src=f.url;i.loading='lazy';c.appendChild(i);"
    " const r=document.createElement('div');r.className='cr';"
    " r.innerHTML='<small>'+f.name.replace(/^frame_/,'').replace(/\\.png$/,'')+'</small>"
    "  <a href=\"'+f.url+'?download=1\">PNG ↓</a>';c.appendChild(r);return c;}"
    "const known=new Set();let firstLoad=true;"
    "async function listLoop(){"
    " try{"
    "  const j=await (await fetch('/api/frames',{cache:'no-store'})).json();"
    "  currentMode=j.mode;"
    "  document.getElementById('c').textContent=j.frames.length;"
    "  document.getElementById('cap').textContent=j.captured;"
    "  document.getElementById('ram').textContent=j.ram_used+'/'+j.ram_slots;"
    "  document.getElementById('heap').textContent=Math.round(j.free_heap/1024)+'K';"
    "  document.getElementById('f').textContent=Math.round(j.free/1024)+'K';"
    "  document.getElementById('addr').textContent=j.addr;"
    "  document.getElementById('drv').textContent=j.driver;"
    "  const dot=document.getElementById('dot'),stt=document.getElementById('stt');"
    "  const pbar=document.getElementById('pbar'),pfill=document.getElementById('pfill');"
    "  if(j.processing){dot.className='dot proc';stt.textContent='рендер '+j.process_idx+'/'+j.process_total;"
    "   pbar.className='bar show';pfill.style.width=(j.process_total?Math.round(100*j.process_idx/j.process_total):0)+'%';"
    "  }else if(j.capture_running){dot.className='dot on';"
    "   stt.textContent='захват '+j.ram_used+'/'+j.ram_slots;"
    "   pbar.className='bar show';pfill.style.width=(j.ram_slots?Math.round(100*j.ram_used/j.ram_slots):0)+'%';"
    "  }else{dot.className='dot';stt.textContent='остановлен';pbar.className='bar';}"
    "  const items=j.frames.slice().sort((a,b)=>b.name.localeCompare(a.name));"
    "  const g=document.getElementById('g');"
    "  if(firstLoad){g.innerHTML='';for(const f of items){known.add(f.name);g.appendChild(card(f));}firstLoad=false;}"
    "  else{for(const f of items){if(known.has(f.name))continue;known.add(f.name);g.insertBefore(card(f),g.firstChild);}"
    "   const alive=new Set(items.map(x=>x.name));"
    "   for(const ch of Array.from(g.children)){if(!alive.has(ch.dataset.name)){known.delete(ch.dataset.name);ch.remove();}}}"
    " }catch(e){}"
    " setTimeout(listLoop,3500);}"
    "async function wifiLoop(){"
    " try{"
    "  const j=await (await fetch('/api/wifi',{cache:'no-store'})).json();"
    "  document.getElementById('apssid').textContent=j.ap_enabled?(j.ap_ssid+' (ON)'):(j.ap_ssid+' (OFF)');"
    "  document.getElementById('apip').textContent=j.ap_enabled?j.ap_ip:'выключен';"
    "  document.getElementById('apcl').textContent=j.ap_enabled?j.ap_clients:'-';"
    "  document.getElementById('stast').textContent=j.sta_configured?(j.sta_connected?('ON '+j.sta_ssid):('OFF '+j.sta_ssid)):'не настроено';"
    "  document.getElementById('staip').textContent=j.sta_connected?j.sta_ip:'-';"
    "  document.getElementById('rssi').textContent=j.sta_connected?(j.sta_rssi+' dBm'):'-';"
    " }catch(e){}"
    " setTimeout(wifiLoop,6000);}"
    "document.getElementById('bstart').addEventListener('click',()=>{"
    " const ms=parseInt(document.getElementById('ms').value)||500;"
    " location.href='/capture/start?ms='+ms;});"
    "document.getElementById('bstop').addEventListener('click',()=>{location.href='/capture/stop';});"
    "fetch('/api/mode').then(r=>r.json()).then(j=>{"
    " currentMode=j.mode;document.getElementById('mn').textContent=j.name;"
    " document.getElementById('addr').textContent=j.addr;"
    " document.getElementById('drv').textContent=j.driver;});"
    "previewLoop();listLoop();wifiLoop();"
    "</script></body></html>"
  );
  server.sendHeader("Cache-Control", "no-store");
  server.sendHeader("Connection", "keep-alive");
  server.send(200, "text/html; charset=utf-8", html);
}

void handleFile() {
  String path = server.uri();
  if (!path.endsWith(".png") || path.indexOf("..") >= 0) {
    server.send(404, "text/plain", "Not found"); return;
  }
  File file = LittleFS.open(path, "r");
  if (!file) { server.send(404, "text/plain", "Not found"); return; }
  if (server.hasArg("download")) {
    String filename = path.substring(path.lastIndexOf('/') + 1);
    server.sendHeader("Content-Disposition", "attachment; filename=\"" + filename + "\"");
  }
  WiFiClient c = server.client(); c.setNoDelay(true);
  server.sendHeader("Connection", "keep-alive");
  server.streamFile(file, "image/png");
  file.close();
}

void setup() {
  Serial.begin(115200);
  delay(300);
  Serial.println();
  Serial.println("OLED Sniffer starting...");

  setCpuFrequencyMhz(CPU_FREQ_MHZ);

  if (!LittleFS.begin(true)) Serial.println("LittleFS mount failed.");
  else {
    loadMode();
    loadAddr();
    loadDriver();
    loadWifiCreds();
    findLastFrameNumber();
    Serial.printf("Prev frame: %lu mode=%u (%s) addr=0x%02X driver=%s heap=%u\n",
                  (unsigned long)frameNumberCounter, (unsigned)activeMode,
                  RENDER_VARIANTS[activeMode].name, oledAddr,
                  driverMode ? "SH1106" : "SSD1306",
                  (unsigned)ESP.getFreeHeap());
    if (staSsid.length() > 0)
      Serial.printf("[wifi] stored STA: %s\n", staSsid.c_str());
  }

  setupWiFi();

  addressingMode = (driverMode == 1) ? 2 : 0;
  restartI2C();

  server.on("/", HTTP_GET, handleIndex);
  server.on("/setmode", HTTP_GET, handleSetMode);
  server.on("/toggle-addr", HTTP_GET, handleToggleAddr);
  server.on("/toggle-driver", HTTP_GET, handleToggleDriver);
  server.on("/wifi/set", HTTP_GET, handleWifiSet);
  server.on("/wifi/forget", HTTP_GET, handleWifiForget);
  server.on("/wifi/reconnect", HTTP_GET, handleWifiReconnect);
  server.on("/api/wifi", HTTP_GET, handleApiWifi);
  server.on("/api/mode", HTTP_GET, handleApiMode);
  server.on("/api/frames", HTTP_GET, handleFrames);
  server.on("/preview.bin", HTTP_GET, handlePreviewBin);
  server.on("/capture/start", HTTP_GET, handleCaptureStart);
  server.on("/capture/stop", HTTP_GET, handleCaptureStop);
  server.on("/files", HTTP_GET, handleFiles);
  server.on("/renders", HTTP_GET, handleRenders);
  server.on("/clear", HTTP_GET, handleClear);
  server.on("/zip", HTTP_GET, handleZip);
  server.onNotFound(handleFile);
  server.begin();
  Serial.println("HTTP server started.");
  Serial.printf("TX power %d dBm, CPU %u MHz\n",
                (int)WIFI_TX_POWER, (unsigned)getCpuFrequencyMhz());
}

void loop() {
  server.handleClient();

  drainI2CRing();

  static uint32_t lastWifiCheck = 0;
  uint32_t nowT = millis();
  if (nowT - lastWifiCheck >= 1000) {
    lastWifiCheck = nowT;
    updateApState();
    bool nowUp = (WiFi.status() == WL_CONNECTED);
    if (nowUp != staWasConnected) {
      staWasConnected = nowUp;
      Serial.printf("[wifi] STA %s%s\n",
                    nowUp ? "up: " : "down",
                    nowUp ? WiFi.localIP().toString().c_str() : "");
    }
  }

  if (captureRunning) {
    uint32_t now = millis();
    if ((int32_t)(now - lastCaptureMs) >= (int32_t)captureIntervalMs) {
      lastCaptureMs = now;
      if (ramHead < ramSlots) {
        portENTER_CRITICAL(&framebufferMux);
        memcpy(ramBuf + (size_t)ramHead * FB_SIZE, framebuffer, FB_SIZE);
        portEXIT_CRITICAL(&framebufferMux);
        ramHead++;
      } else {
        ramFull = true;
        captureRunning = false;
        Serial.printf("[capture] RAM full at %d, starting processing\n", ramSlots);
        startProcessing();
      }
    }
  }

  if (processing) {
    if (abortProcessing) {
      processing = false; abortProcessing = false;
      ramHead = 0; processIdx = 0; processTotal = 0;
      Serial.println("[process] aborted");
    } else if (processIdx < processTotal) {
      uint32_t nextNumber = frameNumberCounter + 1;
      renderFramebuffer(ramBuf + (size_t)processIdx * FB_SIZE, activeMode);
      String pngPath = frameFilename(nextNumber);
      if (savePixPNGToFile(pngPath)) {
        frameNumberCounter = nextNumber;
        capturedCount++;
        pruneOldFrames(frameNumberCounter);
      }
      processIdx++;
      delay(1);
    } else {
      Serial.printf("[process] done, saved %d\n", processTotal);
      processing = false; ramHead = 0; processIdx = 0; processTotal = 0;
    }
  }

  yield();
}