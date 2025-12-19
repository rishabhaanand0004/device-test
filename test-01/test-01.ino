/* 
  ESP32 + Dual MFRC522 (Entry & Exit) + FirebaseClient (Firestore)
  Final version with O(1) lookup for active cards and meta-based sync.
  Small, non-invasive improvements applied:
   - UID_MAX_BYTES macro (safe support up to 16 bytes)
   - Atomic swap protection (portMUX) when updating active-cards / set
   - findActiveCardTimes: check all shifts and optionally test against a target HH:MM
   - /status HTTP endpoint for diagnostics while provisioning portal is active
   - Exponential backoff scheduling on Firebase failures (g_nextFirebaseInitAttempt)
   - Extra diagnostics when a UID is found in set but times lookup fails
*/

#include <Arduino.h>
#include <WiFi.h>
#include <WiFiClientSecure.h>
#include <WebServer.h>          // provisioning portal
#include <SPIFFS.h>
#include <SPI.h>
#include <MFRC522.h>
#include <time.h>
#include <vector>
#include <unordered_set>
#include <string>
#include <algorithm>

#include <sys/time.h> // for settimeofday; already available on ESP32

// -------- FirebaseClient toggles --------
#define ENABLE_FIRESTORE
#define ENABLE_USER_AUTH
#define ENABLE_FS
#define FIREBASE_PRINTF_PORT Serial
#include <FirebaseClient.h>

// ---------------- Prefill for provisioning page ONLY (not auto-saved)
#define API_KEY_PREFILL   "AIzaSyA798vpOSokpRWCcHS08FbgRP7ldczqJ4w"
#define PROJECT_ID_PREFILL "sentri-ban2r1"

// ---------------- Hardware: Dual MFRC522 + Relay ---------
#define MFRC522_ENTRY_SS  5
#define MFRC522_ENTRY_RST 21
#define MFRC522_EXIT_SS   13
#define MFRC522_EXIT_RST  15
#define FACTORY_RESET_PIN   33       // primary reset button
#define RELAY              32       // HIGH = lock; LOW = unlock
#define DOOR_PULSE_MS      3000     // unlock pulse ms

// Technician-only full-wipe pin: must be jumper-to-GND while holding FACTORY_RESET_PIN at boot.
// Set to -1 to disable full-wipe capability.
#ifndef FACTORY_RESET_FULL_PIN
  #define FACTORY_RESET_FULL_PIN 25
#endif

// ---------------- [MOD] UID buffer macro -----------------
#ifndef UID_MAX_BYTES
  #define UID_MAX_BYTES 16
#endif
// ---------------------------------------------------------

const int RELAY_LOCKED_STATE   = LOW;
const int RELAY_UNLOCKED_STATE = HIGH;

MFRC522 rfidEntry(MFRC522_ENTRY_SS, MFRC522_ENTRY_RST);
MFRC522 rfidExit (MFRC522_EXIT_SS,  MFRC522_EXIT_RST);

// ---------------- Firebase client objects
WiFiClientSecure ssl_client;
using AsyncClient = AsyncClientClass;
AsyncClient aClient(ssl_client);

FirebaseApp app;
UserAuth user_auth("", "", "");       // real values loaded after provisioning
Firestore::Documents Docs;

// ---------------- Files & thresholds
static const char* FILE_CONFIG       = "/config.json";
static const char* FILE_CARD_CACHE   = "/cards_cache.ndjson";
static const char* FILE_LOG_QUEUE    = "/access_logs.ndjson";
static const char* FILE_LOG_COUNTER  = "/log_counter.txt";
static const char* FILE_ACTIVITY     = "/activity_state.txt";
static const char* FILE_ACCESS_LIST  = "/access_list.json";
static const char* FILE_ACCESS_META  = "/access_meta.json"; // new meta file with updated_at

// Wi-Fi recovery timing (non-blocking)
// retry Wi-Fi connections for 2 minutes before opening AP
static const unsigned long WIFI_LOOKUP_TIMEOUT_MS = 2UL * 60UL * 1000UL; // 2 minutes

// keep AP/provisioning portal open for 5 minutes
static const unsigned long PROVISION_WINDOW_MS    = 5UL * 60UL * 1000UL; // 5 minutes

static const uint32_t CARD_CACHE_TTL_SEC = 24U * 3600U;  // 24h card cache
static const uint32_t HEARTBEAT_MS       = 60UL * 60UL * 1000UL; // hourly = 60 * 60 * 1000
static const uint32_t FLUSH_INTERVAL_MS  = 1UL * 60UL * 1000UL; // hourly = 60 * 60 * 1000
static const float    FLUSH_FS_THRESH    = 0.80f;                 // 80% SPIFFS

// runtime wifi recovery state
unsigned long g_wifiFailStart = 0;       // when the current "search for wifi" window started
unsigned long g_provWindowStart = 0;     // when the provisioning window started
bool g_inProvWindow = false;             // are we currently serving the provisioning portal?

// Firebase failure handling
int firebaseFailCount = 0;
const int FIREBASE_FAIL_THRESHOLD = 5;          // after this many failures -> open AP
const unsigned long FIREBASE_FAIL_RESET_MS = 5 * 60UL * 1000UL; // reset fail counter after 5 minutes
unsigned long firebaseLastFailAt = 0;

// Non-blocking Firebase init helpers
void firebaseInitStart();
void firebaseInitPoll();

// Request flag to start Firebase init from main loop (set from Wi-Fi event)
bool g_requestFirebaseInit = false;

// ---------------- Runtime state (populated from /config.json after provisioning)
String g_ssid, g_pass, g_apiKey, g_projectId, g_userEmail, g_userPass, g_businessId, g_deviceName;
String g_mac;
bool   g_activityEnabled = true;  // true=normal (locked & pulse on grant), false=held unlocked
unsigned long g_lastHeartbeat = 0;
unsigned long g_lastFlush     = 0;

// Runtime reset state (non-blocking)
unsigned long g_resetPressStart = 0;   // when button first seen pressed
bool g_resetArmed = false;             // true while waiting for release after trigger
const unsigned long RESET_CONFIRM_MS = 3000UL; // require 3s hold to confirm reset

const unsigned long RESET_SHORT_MS = 1000UL;  // >=1s on release => soft restart
const unsigned long RESET_LONG_MS  = 5000UL;  // >=5s on release => remove config (and optional full wipe)

// Non-blocking firebase init state
bool g_firebaseInitInProgress = false;
unsigned long g_firebaseInitStartedAt = 0;
const unsigned long FIREBASE_INIT_POLL_TIMEOUT_MS = 15000UL; // try ~15s before giving up this attempt
const unsigned long FIREBASE_INIT_POLL_SLICE_MS = 200;      // poll slice interval
unsigned long g_lastFirebasePoll = 0;

// GOT_IP / firebase init scheduling
unsigned long g_gotIpAt = 0;                   // millis() when GOT_IP seen
unsigned long g_nextFirebaseInitAttempt = 0;   // earliest millis() to next attempt (backoff)
const unsigned long GOT_IP_INIT_DELAY_MS = 700; // wait 700ms after GOT_IP before calling initializeApp()
const unsigned long FIREBASE_INIT_RETRY_MS = 5000; // retry delay after a failed init attempt

// ---------------- Provisioning portal
WebServer portal(80);
const char* AP_PASS = "12345678";
bool g_portalActive = false;
bool g_portalHandlersRegistered = false;

// Force-provisioning window (used when Firebase auth keeps failing)
unsigned long g_forcedProvUntil = 0; // millis() until which portal must remain open
const unsigned long FIREBASE_PROVISION_WINDOW_MS = 300000UL; // 5 minutes

// --------- Utility declarations (order matters for some callbacks)
void stopProvisionPortal();
void startProvisionPortal(unsigned long forcedWindowMs = 0);
void WiFiEventCB(WiFiEvent_t event);
bool wifiConnect();
void wifiRecoveryTick();
String escapeJson(const String &s);
void timeSync();

// ---------------- Active cards structures and O(1) lookup
struct ActiveCardEntry {
  String card_data;
  String start_time; // "HH:MM"
  String end_time;   // "HH:MM"
};
std::vector<ActiveCardEntry> g_activeCards;
const size_t MAX_ACTIVE_CARDS = 1024;

// O(1) lookup set using UPPERCASE ASCII strings for fast membership tests
static std::unordered_set<std::string> g_activeSet;

// ---------------- [MOD] small mutex for atomic swap protection ----------------
// Protect g_activeCards / g_activeSet updates with a portMUX critical section.
portMUX_TYPE g_activeCardsMux = portMUX_INITIALIZER_UNLOCKED;
bool g_updatingActiveCards = false; // diagnostic flag
// ---------------------------------------------------------------------------------

// ---------------- Utilities (SPIFFS, time, Wi-Fi)
bool fsEnsure() {
  Serial.println("Mounting SPIFFS...");
  // First try a normal mount
  if (SPIFFS.begin()) {
    Serial.println("SPIFFS mounted (normal).");
    Serial.printf("SPIFFS: used=%u total=%u\n", (unsigned)SPIFFS.usedBytes(), (unsigned)SPIFFS.totalBytes());
    return true;
  }

  Serial.println("SPIFFS mount failed (normal). Trying mount with format fallback...");
  // Try mounting with format-on-failure (this will create a new empty FS if the old one is corrupt)
  if (SPIFFS.begin(true)) { // true => format if mount fails (Arduino core behavior)
    Serial.println("SPIFFS mounted after format.");
    Serial.printf("SPIFFS: used=%u total=%u\n", (unsigned)SPIFFS.usedBytes(), (unsigned)SPIFFS.totalBytes());
    return true;
  }

  // Final retry after end() in case driver left in a bad state
  Serial.println("SPIFFS.begin(true) failed. Calling SPIFFS.end() and retrying once...");
  SPIFFS.end();
  delay(100);
  if (SPIFFS.begin(true)) {
    Serial.println("SPIFFS mounted after end()+format retry.");
    Serial.printf("SPIFFS: used=%u total=%u\n", (unsigned)SPIFFS.usedBytes(), (unsigned)SPIFFS.totalBytes());
    return true;
  }

  // All attempts failed — provide guidance and do not attempt destructive actions
  Serial.println("SPIFFS mount failed after multiple attempts.");
  Serial.println("Possible causes:");
  Serial.println("  - No SPIFFS partition in partition table / selected partition scheme");
  Serial.println("  - Flash content corrupted / incompatible format (LittleFS vs SPIFFS)");
  Serial.println("  - Mismatch of flash size or flash mode at build time");
  Serial.println();
  Serial.println("Recommended next steps:");
  Serial.println("  1) Check your Partition Scheme (Arduino IDE: Tools > Partition Scheme).");
  Serial.println("     Select a scheme that includes SPIFFS (eg: \"Default 4MB with spiffs\").");
  Serial.println("  2) If using PlatformIO, ensure platformio.ini defines a partition table with a spiffs partition");
  Serial.println("     or use built-in scheme: board_build.partitions = default.csv or a spiffs-enabled csv.");
  Serial.println("  3) If the device was previously flashed with LittleFS, reformat flash or update code to use LittleFS.");
  Serial.println("  4) As a last resort (will erase all flash), run: esptool.py --chip esp32 erase_flash  (use with caution).");
  Serial.println();
  return false;
}

// Normalize UID/card_data to canonical uppercase hex without whitespace
String normalizeUidStr(const String &s) {
  String out;
  out.reserve(s.length());
  for (size_t i = 0; i < s.length(); ++i) {
    char c = s[i];
    // accept hex digits only; ignore whitespace/other separators
    if ((c >= '0' && c <= '9') ||
        (c >= 'A' && c <= 'F') ||
        (c >= 'a' && c <= 'f')) {
      if (c >= 'a' && c <= 'f') c = c - ('a' - 'A');
      out += c;
    }
  }
  return out;
}

bool fileExists(const char* p) { return SPIFFS.exists(p); }
size_t fsUsed()  { return SPIFFS.usedBytes(); }
size_t fsTotal() { return SPIFFS.totalBytes(); }
float  fsUsage() { return fsTotal() ? (float)fsUsed() / (float)fsTotal() : 0.0f; }

String readFile(const char* path) {
  File f = SPIFFS.open(path, "r");
  if (!f) return "";
  String s = f.readString();
  f.close();
  return s;
}
bool writeFile(const char* path, const String& data) {
  File f = SPIFFS.open(path, "w");
  if (!f) return false;
  f.print(data);
  f.close();
  return true;
}
bool appendLine(const char* path, const String& line) {
  File f = SPIFFS.open(path, "a");
  if (!f) return false;
  f.println(line);
  f.close();
  return true;
}

String trimStr(const String &s) {
  String out = s;
  // remove leading whitespace
  while (out.length() && (out[0] == ' ' || out[0] == '\r' || out[0] == '\n' || out[0] == '\t')) out = out.substring(1);
  // remove trailing whitespace
  while (out.length() && (out[out.length()-1] == ' ' || out[out.length()-1] == '\r' || out[out.length()-1] == '\n' || out[out.length()-1] == '\t')) out = out.substring(0, out.length()-1);
  return out;
}

String rfc3339NowUTC() {
  time_t now = time(nullptr);
  struct tm* tm_utc = gmtime(&now);
  char buf[32];
  strftime(buf, sizeof(buf), "%Y-%m-%dT%H:%M:%SZ", tm_utc);
  return String(buf);
}

// escape double quotes and backslashes so JSON isn't broken by user input
String escapeJson(const String &s) {
  String out;
  out.reserve(s.length());
  for (size_t i = 0; i < s.length(); ++i) {
    char c = s[i];
    if (c == '\"')  { out += "\\\\\""; }
    else if (c == '\\') { out += "\\\\\\\\"; }
    else out += c;
  }
  return out;
}

String currentHHMM() {
  time_t now = time(nullptr);
  struct tm *tm_local = localtime(&now);
  char buf[6];
  snprintf(buf, sizeof(buf), "%02d:%02d", tm_local->tm_hour, tm_local->tm_min);
  return String(buf);
}

bool timeInRange(const String &startHHMM, const String &endHHMM, const String &targetHHMM) {
  auto toMin = [](const String &s)->int {
    if (s.length() < 4) return -1;
    int h = s.substring(0,2).toInt();
    int m = s.substring(3,5).toInt();
    return h*60 + m;
  };
  int s = toMin(startHHMM);
  int e = toMin(endHHMM);
  int t = toMin(targetHHMM);
  if (s<0 || e<0 || t<0) return false;
  if (s <= e) return (t >= s && t <= e);
  // overnight e.g. 22:00-06:00 -> allow if t >= s OR t <= e
  return (t >= s || t <= e);
}

// ---------------- Config load/check (NO seeding; only read if exists)
String jsonGetStr(const String& json, const String& key) {
  // Lightweight extractor: finds "key":"value"
  String kq="\""+key+"\":";
  int k=json.indexOf(kq); if(k<0) return "";
  int q1=json.indexOf('"',k+kq.length()); if(q1<0) return "";
  int q2=json.indexOf('"',q1+1);          if(q2<0) return "";
  return json.substring(q1+1,q2);
}
void loadConfigIfPresent() {
  if (!fileExists(FILE_CONFIG)) {
    // keep all fields empty; portal will collect them
    g_ssid = g_pass = g_apiKey = g_projectId = g_userEmail = g_userPass = g_businessId = g_deviceName = "";
    return;
  }

  String cfg = readFile(FILE_CONFIG);

  // Extract then trim each field to remove hidden whitespace/newlines from user input
  g_ssid       = trimStr(jsonGetStr(cfg, "wifi_ssid"));
  g_pass       = trimStr(jsonGetStr(cfg, "wifi_password"));
  g_apiKey     = trimStr(jsonGetStr(cfg, "api_key"));
  g_projectId  = trimStr(jsonGetStr(cfg, "project_id"));
  g_userEmail  = trimStr(jsonGetStr(cfg, "user_email"));
  g_userPass   = trimStr(jsonGetStr(cfg, "user_password"));
  g_businessId = trimStr(jsonGetStr(cfg, "business_id"));
  g_deviceName = trimStr(jsonGetStr(cfg, "device_name"));
}

bool configComplete() {
  return g_ssid.length() && g_pass.length() &&
         g_apiKey.length() && g_projectId.length() &&
         g_userEmail.length() && g_userPass.length() &&
         g_businessId.length();
}

// ---------------- Provisioning portal (AP mode)
String apSSID() {
  return "Sentri-Setup";
}

void timeSync() {
  if (WiFi.status() != WL_CONNECTED) {
    Serial.println("timeSync(): WiFi not connected; skipping NTP sync.");
    return;
  }

  // Set timezone to IST (UTC+5:30)
  setenv("TZ", "IST-5:30", 1);
  tzset();

  const char* ntpServers[] = { "time.google.com", "pool.ntp.org", "time.nist.gov" };
  const int maxAttempts = 15;
  bool sntpOK = false;

  Serial.print("Syncing time (SNTP) ");

  // Use GMT offset = 0 since timezone is already set via TZ
  configTime(0, 0, ntpServers[0], ntpServers[1], ntpServers[2]);

  for (int a = 0; a < maxAttempts; ++a) {
    time_t now = time(nullptr);
    if (now > 1577836800) {
      sntpOK = true;
      break;
    }
    delay(2000);  // Wait 2 seconds per attempt
    Serial.print('.');
  }

  if (sntpOK) {
    Serial.println(" SNTP OK");
    Serial.printf("Local time now: %s\n", currentHHMM().c_str());
    return;
  }

  Serial.println();
  Serial.println("SNTP sync failed. Running diagnostics & HTTP fallback...");

  // DNS diagnostics
  for (int i = 0; i < 3; ++i) {
    IPAddress ip;
    bool ok = WiFi.hostByName(ntpServers[i], ip);
    Serial.printf("DNS: %-16s -> %s\n", ntpServers[i], 
                  ok ? ip.toString().c_str() : "FAILED");
  }

  // HTTP fallback
  Serial.print("HTTP fallback: contacting worldtimeapi.org ... ");
  WiFiClient client;
  
  if (!client.connect("worldtimeapi.org", 80)) {
    Serial.println("connect FAILED");
    return;
  }

  client.print("GET /api/ip HTTP/1.0\r\n"
               "Host: worldtimeapi.org\r\n"
               "Connection: close\r\n\r\n");

  unsigned long start = millis();
  String resp = "";
  while (client.connected() && (millis() - start) < 5000) {
    if (client.available()) {
      resp += client.readStringUntil('\n') + '\n';
      start = millis();
    }
  }
  client.stop();

  // Parse unixtime
  int pos = resp.indexOf("\"unixtime\"");
  if (pos >= 0) {
    int colon = resp.indexOf(':', pos);
    if (colon >= 0) {
      String numStr = "";
      for (int i = colon + 1; i < resp.length(); i++) {
        if (isDigit(resp[i])) numStr += resp[i];
        else if (numStr.length() > 0) break;
      }
      
      if (numStr.length() > 0) {
        unsigned long epoch = strtoul(numStr.c_str(), NULL, 10);
        struct timeval tv = { .tv_sec = (time_t)epoch, .tv_usec = 0 };
        
        if (settimeofday(&tv, NULL) == 0) {
          Serial.printf("HTTP fallback OK. Local time: %s\n", currentHHMM().c_str());
          return;
        }
      }
    }
  }

  Serial.println("HTTP fallback failed - could not parse time.");
}

void handleRoot() {
  // Prefill: use configured values if present; else use PREFILL for API/Project only
  String apiPrefill  = g_apiKey.length()    ? g_apiKey    : String(API_KEY_PREFILL);
  String projPrefill = g_projectId.length() ? g_projectId : String(PROJECT_ID_PREFILL);

  String page =
    "<!doctype html><html><head><meta charset='utf-8'/>"
    "<title>Sentri Setup</title>"
    "<style>body{font-family:system-ui;margin:20px;max-width:800px}"
    "input,textarea{width:100%;padding:8px;margin:6px 0}button{padding:10px 16px}</style>"
    "</head><body>"
    "<h2>Sentri Device Setup</h2>"
    "<form method='POST' action='/save'>"
    "<h3>Wi-Fi</h3>"
    "<label>SSID</label><input name='wifi_ssid' value='" + g_ssid + "'/>"
    "<label>Password</label><input name='wifi_password' type='password' value='" + g_pass + "'/>"
    "<h3>Firebase</h3>"
    "<label>API Key</label><input name='api_key' value='" + apiPrefill + "'/>"
    "<label>Project ID</label><input name='project_id' value='" + projPrefill + "'/>"
    "<label>User Email</label><input name='user_email' value='" + g_userEmail + "'/>"
    "<label>User Password</label><input name='user_password' type='password' value='" + g_userPass + "'/>"
    "<label>Business ID</label><input name='business_id' value='" + g_businessId + "'/>"
    "<label>Device Name</label><input name='device_name' value='" + g_deviceName + "' placeholder='e.g., Main Gate'/>"
    "<br/><button type='submit'>Save & Reboot</button>"
    "</form>"
    "<p style='opacity:.7;margin-top:16px'>AP SSID: " + apSSID() + " — MAC: " + g_mac + "</p>"
    "<p style='opacity:.7;margin-top:8px'><a href='/status'>/status (diagnostics)</a></p>"
    "</body></html>";
  portal.send(200, "text/html", page);
}
void handleSave() {
  // Save exactly what user entered (no hidden defaults)
  String cfg = "{";
  cfg += "\"wifi_ssid\":\""    + escapeJson(portal.arg("wifi_ssid"))    + "\","; 
  cfg += "\"wifi_password\":\""+ escapeJson(portal.arg("wifi_password")) + "\","; 
  cfg += "\"api_key\":\""      + escapeJson(portal.arg("api_key"))      + "\","; 
  cfg += "\"project_id\":\""   + escapeJson(portal.arg("project_id"))   + "\","; 
  cfg += "\"user_email\":\""   + escapeJson(portal.arg("user_email"))   + "\","; 
  cfg += "\"user_password\":\""+ escapeJson(portal.arg("user_password"))+ "\","; 
  cfg += "\"business_id\":\""  + escapeJson(portal.arg("business_id"))  + "\","; 
  cfg += "\"device_name\":\""  + escapeJson(portal.arg("device_name"))  + "\"";
  cfg += "}";

  // write atomically to tmp then rename with fallback
  const char* tmp = "/config.tmp";
  if (writeFile(tmp, cfg)) {
    bool renamed = SPIFFS.rename(tmp, FILE_CONFIG);
    if (!renamed) {
      // fallback: read tmp and write to final
      String t = readFile(tmp);
      if (t.length()) {
        if (SPIFFS.exists(FILE_CONFIG)) SPIFFS.remove(FILE_CONFIG);
        writeFile(FILE_CONFIG, t);
        SPIFFS.remove(tmp);
        Serial.println("Config saved (fallback overwrite).");
      } else {
        Serial.println("Failed to save config: tmp read empty.");
      }
    } else {
      Serial.println("Config saved (rename).");
    }
  } else {
    Serial.println("Failed to write tmp config");
  }

  // debug: print saved config (temporary - remove after verifying)
  Serial.println("=== SAVED CONFIG START ===");
  Serial.println(readFile(FILE_CONFIG));
  Serial.println("=== SAVED CONFIG END ===");

  portal.send(200, "text/html",
    "<html><body><h3>Saved. Rebooting...</h3>"
    "<script>setTimeout(()=>{fetch('/reboot')},800);</script></body></html>");
}
void handleReboot() {
  portal.send(200, "text/plain", "Rebooting");
  delay(200);
  ESP.restart();
}

// ---------------- [MOD] /status endpoint for diagnostics ----------------
void handleStatus() {
  String s = "{";
  s += "\"mac\":\"" + g_mac + "\",";
  s += "\"wifi_status\":" + String(WiFi.status()) + ",";
  s += "\"ip\":\"" + WiFi.localIP().toString() + "\",";
  s += "\"rssi\":" + String(WiFi.RSSI()) + ",";
  s += "\"firebase_ready\":" + String(app.ready() ? "true" : "false") + ",";
  s += "\"active_cards_loaded\":" + String((unsigned)g_activeCards.size()) + ",";
  s += "\"active_set_size\":" + String((unsigned)g_activeSet.size()) + ",";
  s += "\"activity_enabled\":" + String(g_activityEnabled ? "true" : "false") + ",";
  s += "\"last_heartbeat_ms\":" + String(g_lastHeartbeat) + ",";
  s += "\"last_flush_ms\":" + String(g_lastFlush) + ",";
  s += "\"firebase_fail_count\":" + String(firebaseFailCount);
  s += "}";
  portal.send(200, "application/json", s);
}
// ---------------------------------------------------------------------------

// ---------------- Helpers for active_cards meta parsing ----------------

// Extract a timestamp-like string for a field (attempts several patterns)
String fsGetTimestampField(const String &json, const char *field) {
  // Looks for either:
  // "field": { "timestampValue": "2025-10-14T19:19:19.733Z" }
  // or top-level "updateTime": "2025-10-14T19:19:19.733Z"
  String key = "\"" + String(field) + "\"";
  int k = json.indexOf(key);
  if (k >= 0) {
    int tv = json.indexOf("\"timestampValue\"", k);
    if (tv >= 0) {
      int colon = json.indexOf(':', tv);
      if (colon >= 0) {
        int q1 = json.indexOf('"', colon);
        if (q1 >= 0) {
          int q2 = json.indexOf('"', q1+1);
          if (q2 >= 0) return json.substring(q1+1, q2);
        }
      }
    }
    // fallback: maybe field was written differently; search for first quoted value after field
    int q1 = json.indexOf('"', k + key.length());
    if (q1 >= 0) {
      int q2 = json.indexOf('"', q1+1);
      if (q2 >= 0) {
        String candidate = json.substring(q1+1, q2);
        // basic sanity: contains 'T' and '-' and ':'
        if (candidate.indexOf('T') >= 0 && candidate.indexOf(':') >= 0) return candidate;
      }
    }
  }

  // fallback: try updateTime (top-level metadata field returned by SDK)
  int ut = json.indexOf("\"updateTime\"");
  if (ut >= 0) {
    int q1 = json.indexOf('"', ut + 12);
    q1 = json.indexOf('"', q1 + 1);
    int q2 = json.indexOf('"', q1 + 1);
    if (q1 >= 0 && q2 >= 0) return json.substring(q1+1, q2);
  }

  return String("");
}

void writeAccessMeta(const String &updated_at) {
  String meta = "{\"updated_at\":\"" + updated_at + "\"}";
  writeFile(FILE_ACCESS_META, meta);
}

// ---------------- Replacement fetchActiveCardsFromFirebase (v2) ----------------
void fetchActiveCardsFromFirebase_v2() {
  if (!(WiFi.status() == WL_CONNECTED && app.ready() && g_businessId.length())) {
    Serial.println("fetchActiveCardsFromFirebase_v2: skipping (offline or not ready).");
    return;
  }

  String docPath = "businessess/" + g_businessId + "/active_cards/active_cards";
  Serial.println("Fetching active_cards from Firestore...");
  String payload = Docs.get(aClient, Firestore::Parent(g_projectId), docPath, GetDocumentOptions());
  int err = aClient.lastError().code();
  if (err != 0) {
    Serial.printf("fetchActiveCardsFromFirebase_v2: transport error: %s\n", aClient.lastError().message().c_str());
    return;
  }

  // 1) Extract remote updated_at (timestamp string)
  String remoteUpdated = fsGetTimestampField(payload, "updated_at");
  if (remoteUpdated.length() == 0) {
    Serial.println("fetchActiveCardsFromFirebase_v2: remote updated_at missing -> will fetch and replace.");
  }

  // 2) Read local meta updated_at
  String localMeta = readFile(FILE_ACCESS_META);
  String localUpdated = "";
  if (localMeta.length()) localUpdated = jsonGetStr(localMeta, "updated_at");

  // 3) If remoteUpdated exists and equals local -> nothing to do
  if (remoteUpdated.length() && localUpdated.length() && remoteUpdated == localUpdated) {
    Serial.println("fetchActiveCardsFromFirebase_v2: updated_at unchanged -> skipping download.");
    return;
  }

  // Robust helper (local lambda) to extract a string value for a given key starting at a given position.
  auto extractStringValueNear = [&](const String &json, const char *key, int startPos)->String {
    String sKey = String("\"") + key + "\"";
    int k = json.indexOf(sKey, startPos);
    if (k < 0) return String("");

    // Prefer the canonical Firestore shape: "key": { "stringValue": "VALUE" }
    int sv = json.indexOf("\"stringValue\"", k);
    if (sv >= 0) {
      int colon = json.indexOf(':', sv);
      if (colon >= 0) {
        int q1 = json.indexOf('"', colon + 1);
        if (q1 >= 0) {
          int q2 = json.indexOf('"', q1 + 1);
          if (q2 >= 0) {
            return json.substring(q1 + 1, q2);
          }
        }
      }
    }

    // Fallback: find the first quoted string after the key (looser)
    int q1 = json.indexOf('"', k + sKey.length());
    if (q1 < 0) return String("");
    int q2 = json.indexOf('"', q1 + 1);
    if (q2 < 0) return String("");
    // Return the quoted substring but be conservative: if it looks like a structural token (":", "{", "}") treat empty
    String candidate = json.substring(q1 + 1, q2);
    // sanity check
    if (candidate.length() < 1) return String("");
    return candidate;
  };

  // 4) Remote changed (or missing) -> parse cards array from payload
  Serial.println("fetchActiveCardsFromFirebase_v2: downloading and parsing cards array...");
  std::vector<ActiveCardEntry> newList;
  newList.clear();

  int pos = 0;
  // The Firestore document contains an array under fields.cards.arrayValue.values[], but we don't rely on the exact nesting
  // We iterate over occurrences of "card_data" and extract the values near each occurrence.
  while (pos < (int)payload.length()) {
    int cdKey = payload.indexOf("\"card_data\"", pos);
    if (cdKey < 0) break;

    // Extract card_data robustly
    String card = extractStringValueNear(payload, "card_data", cdKey);
    // Extract start_time and end_time that are *nearby* (search from cdKey forward)
    String st = extractStringValueNear(payload, "start_time", cdKey);
    if (st.length() == 0) st = "00:00";
    String et = extractStringValueNear(payload, "end_time", cdKey);
    if (et.length() == 0) et = "23:59";

    ActiveCardEntry e;
    e.card_data = card;
    e.start_time = st;
    e.end_time   = et;
    newList.push_back(e);

    // advance pos beyond this card_data occurrence to avoid infinite loop
    pos = cdKey + 11;
    if (newList.size() >= MAX_ACTIVE_CARDS) break;
  }

  // 5) Replace in-memory list atomically (small critical section)
  portENTER_CRITICAL(&g_activeCardsMux);
  g_updatingActiveCards = true;
  g_activeCards.clear();
  g_activeSet.clear();
  for (const auto &entry : newList) {
    // Keep raw card_data in g_activeCards for times lookup and diagnostics
    g_activeCards.push_back(entry);

    // Normalize and insert into set (skip empty)
    String norm = normalizeUidStr(entry.card_data);
    if (norm.length()) {
      std::string s = std::string(norm.c_str());
      g_activeSet.insert(s);
    }
  }
  g_updatingActiveCards = false;
  portEXIT_CRITICAL(&g_activeCardsMux);

  // 6) Persist access_list.json (human-readable)
  {
    String out = "[";
    for (size_t i = 0; i < g_activeCards.size(); ++i) {
      if (i) out += ",";
      out += "{\"card_data\":\"" + g_activeCards[i].card_data + "\"";
      out += ",\"start_time\":\"" + g_activeCards[i].start_time + "\"";
      out += ",\"end_time\":\""   + g_activeCards[i].end_time   + "\"}";
    }
    out += "]";
    writeFile(FILE_ACCESS_LIST, out);
    Serial.printf("Saved %u active cards to %s\n", (unsigned)g_activeCards.size(), FILE_ACCESS_LIST);
  }

  // 7) Persist meta updated_at (use remote if present, else current time)
  String toWriteUpdated = remoteUpdated;
  if (toWriteUpdated.length() == 0) {
    toWriteUpdated = rfc3339NowUTC();
  }
  writeAccessMeta(toWriteUpdated);

  // Diagnostic logging so you can inspect normalized values
  Serial.printf("fetchActiveCardsFromFirebase_v2: updated in-memory list (%u entries), saved meta.\n",
                (unsigned)g_activeCards.size());
  Serial.printf("  g_activeSet size=%u\n", (unsigned)g_activeSet.size());
  for (size_t i = 0; i < g_activeCards.size() && i < 12; ++i) {
    String raw = g_activeCards[i].card_data;
    String nrm = normalizeUidStr(raw);
    Serial.printf("  sample[%u]: raw='%s' norm='%s' start=%s end=%s\n",
                  (unsigned)i, raw.c_str(), nrm.c_str(),
                  g_activeCards[i].start_time.c_str(), g_activeCards[i].end_time.c_str());
  }
}

// ---------------- [MOD] Helper: findActiveCardTimes checks ALL entries for a UID and can test against a target HH:MM.
// If checkTargetHHMM is non-empty it returns the first matching shift that contains the target time.
// Otherwise it returns the first shift found for that UID (for diagnostics).
bool findActiveCardTimes(const String &uid, const String &checkTargetHHMM, String &outStart, String &outEnd) {
  String nuid = normalizeUidStr(uid);
  if (nuid.length() == 0) return false;

  bool anyFound = false;
  for (auto &e : g_activeCards) {
    String ne = normalizeUidStr(e.card_data);
    if (ne == nuid) {
      anyFound = true;
      if (checkTargetHHMM.length()) {
        if (timeInRange(e.start_time, e.end_time, checkTargetHHMM)) {
          outStart = e.start_time;
          outEnd   = e.end_time;
          return true;
        }
      } else {
        outStart = e.start_time;
        outEnd   = e.end_time;
        return true;
      }
    }
  }

  // If at least one entry exists but none matched the target, return first entry (for diagnostics) but report false.
  if (anyFound) {
    for (auto &e : g_activeCards) {
      String ne = normalizeUidStr(e.card_data);
      if (ne == nuid) {
        outStart = e.start_time;
        outEnd   = e.end_time;
        break;
      }
    }
  }
  return false;
}
// ----------------------------------------------------------------------------

// ---------------- Provisioning portal functions (startProvisionPortal/stopProvisionPortal) ----------------
void startProvisionPortal(unsigned long forcedWindowMs) {
  if (g_portalActive) {
    // already active: if a new forced window was requested, extend it
    if (forcedWindowMs > 0) {
      g_forcedProvUntil = millis() + forcedWindowMs;
      Serial.printf("Extending forced provisioning window until +%lus\n", forcedWindowMs / 1000);
    }
    return;
  }

  Serial.println("\n*** Starting Provisioning Portal ***");

  // Ensure Wi-Fi is in AP+STA so we can serve the portal while STA tries reconnecting
  WiFi.mode(WIFI_AP_STA);
  WiFi.softAP(apSSID().c_str(), AP_PASS);
  delay(200);

  // Register handlers only once
  if (!g_portalHandlersRegistered) {
    portal.on("/", HTTP_GET, handleRoot);
    portal.on("/save", HTTP_POST, handleSave);
    portal.on("/reboot", HTTP_GET, handleReboot);
    portal.on("/status", HTTP_GET, handleStatus); // added diagnostics endpoint
    g_portalHandlersRegistered = true;
  }

  portal.begin();

  // bookkeeping
  g_portalActive = true;
  g_inProvWindow = true;
  g_provWindowStart = millis();

  if (forcedWindowMs > 0) {
    g_forcedProvUntil = millis() + forcedWindowMs;
    // clear transient firebase failures so operator is not repeatedly bounced back
    firebaseFailCount = 0;
    firebaseLastFailAt = 0;
    Serial.printf("Provisioning portal FORCED for %lu seconds.\n", forcedWindowMs / 1000);
  } else {
    g_forcedProvUntil = 0;
    Serial.println("Provisioning portal started (normal window).");
  }

  // restart lookup timer after portal ends (fresh lookup window)
  g_wifiFailStart = 0;

  Serial.println("\n=== Provisioning Mode ===");
  Serial.printf("Connect to AP: %s  (pass: %s)\n", apSSID().c_str(), AP_PASS);
}

void stopProvisionPortal() {
  if (!g_portalActive) return;
  Serial.println("Stopping provisioning portal...");
  portal.stop();
  WiFi.softAPdisconnect(true);     // stop AP
  WiFi.mode(WIFI_STA);

  g_portalActive = false;
  // Clear provisioning state so recovery logic behaves consistently.
  g_inProvWindow = false;
  g_provWindowStart = 0;
  delay(50); // let WiFi driver settle
}

// ---------------- Firebase async callback (with light backoff scheduling) ----------------
void asyncCB(AsyncResult &r) {
  // EVENT-level messages (SDK high-level events)
  if (r.isEvent()) {
    String msg = r.appEvent().message();
    int code = r.appEvent().code();
    Firebase.printf("[Evt] %s (%d)\n", msg.c_str(), code);

    String lmsg = msg;
    lmsg.toLowerCase();

    // Treat 400/Bad Request as auth/config failure
    if (lmsg.indexOf("400") >= 0 || lmsg.indexOf("bad request") >= 0 || lmsg.indexOf("permission_denied") >= 0) {
      firebaseFailCount++;
      firebaseLastFailAt = millis();
      // Exponential-ish backoff min(1s * 2^n, 60s)
      int exp = firebaseFailCount;
      if (exp > 12) exp = 12;
      unsigned long backoff = (1UL << exp) * 1000UL;
      if (backoff > 60000UL) backoff = 60000UL;
      g_nextFirebaseInitAttempt = millis() + backoff;
      Serial.printf("Firebase failure #%d detected (msg: %s). Backing off %lums\n", firebaseFailCount, msg.c_str(), backoff);
    } else if (lmsg.indexOf("authenticated") >= 0 || lmsg.indexOf("auth success") >= 0 || code == 0) {
      if (firebaseFailCount > 0) {
        Serial.println("Firebase auth success — clearing failure counter.");
      }
      firebaseFailCount = 0;
      firebaseLastFailAt = 0;
    }
  }
  // ERRORS surfaced by SDK (lower-level)
  if (r.isError()) {
    String em = r.error().message();
    int ec = r.error().code();
    Firebase.printf("[Err] %s (%d)\n", em.c_str(), ec);

    String lem = em;
    lem.toLowerCase();
    if (lem.indexOf("400") >= 0 || lem.indexOf("bad request") >= 0 || lem.indexOf("permission_denied") >= 0) {
      firebaseFailCount++;
      firebaseLastFailAt = millis();
      int exp = firebaseFailCount;
      if (exp > 12) exp = 12;
      unsigned long backoff = (1UL << exp) * 1000UL;
      if (backoff > 60000UL) backoff = 60000UL;
      g_nextFirebaseInitAttempt = millis() + backoff;
      Serial.printf("Firebase error counted as failure #%d (%s). Backing off %lums\n", firebaseFailCount, em.c_str(), backoff);
    }
  }
  // PAYLOAD (if any data is available)
  if (r.available()) {
    Firebase.printf("[Payload] %s\n", r.c_str());
  }
}

// ---------------- Firebase init (DEV TLS: insecure)
// Start firebase initialization (non-blocking)
void firebaseInitStart() {
  if (g_firebaseInitInProgress) return;
  Serial.println("Starting Firebase init (non-blocking start).");
  user_auth = UserAuth(g_apiKey, g_userEmail, g_userPass);
  ssl_client.setInsecure(); // dev path
  initializeApp(aClient, app, getAuth(user_auth), 30000, asyncCB);

  g_firebaseInitInProgress = true;
  g_firebaseInitStartedAt = millis();
  g_lastFirebasePoll = 0;
}

// Poll firebase initialization - call from loop() frequently but non-blocking
void firebaseInitPoll() {
  if (!g_firebaseInitInProgress) return;

  unsigned long now = millis();

  // Give SDK a short slice to progress
  if (now - g_lastFirebasePoll >= FIREBASE_INIT_POLL_SLICE_MS) {
    g_lastFirebasePoll = now;
    app.loop();
    Docs.loop();
  }

  // If ready, finish initialization
  if (app.ready()) {
    Serial.println("Firebase init completed (app.ready()).");
    app.getApp<Firestore::Documents>(Docs);
    g_firebaseInitInProgress = false;
    firebaseFailCount = 0;
    firebaseLastFailAt = 0;

    // Fetch active_cards immediately so device has up-to-date list at boot/ready
    fetchActiveCardsFromFirebase_v2();

    // If provisioning portal is active, close it now that Firebase is good
    if (g_portalActive) {
      Serial.println("Firebase ready — stopping provisioning portal.");
      stopProvisionPortal();
      g_forcedProvUntil = 0;
      g_inProvWindow = false;
      g_provWindowStart = 0;
    }
    return;
  }

  // Timeout for this attempt
  if (now - g_firebaseInitStartedAt >= FIREBASE_INIT_POLL_TIMEOUT_MS) {
    Serial.println("Firebase init attempt timed out (poll). Marking init as failed for now.");
    g_firebaseInitInProgress = false;
    // Record failure
    firebaseFailCount++;
    firebaseLastFailAt = now;
    // Backoff next attempt a bit to allow TCP/IP/wifi to settle
    // Larger backoff if repeated failures
    int exp = firebaseFailCount;
    if (exp > 12) exp = 12;
    unsigned long backoff = (1UL << exp) * 1000UL;
    if (backoff > 60000UL) backoff = 60000UL;
    g_nextFirebaseInitAttempt = now + backoff;
    Serial.printf("Next Firebase init attempt delayed for %lums.\n", backoff);
  }
}

// Called early from loop() to decide whether to force provisioning AP when Firebase auth keeps failing.
void checkFirebaseFailureState() {
  if (firebaseFailCount == 0) return;

  // expire stale failures
  if (firebaseLastFailAt != 0 && millis() - firebaseLastFailAt > FIREBASE_FAIL_RESET_MS) {
    Serial.println("Firebase failures expired — resetting counter.");
    firebaseFailCount = 0;
    firebaseLastFailAt = 0;
    return;
  }

  if (firebaseFailCount >= FIREBASE_FAIL_THRESHOLD && !g_portalActive) {
    Serial.printf("Firebase failures >= %d — forcing provisioning AP for %lu seconds.\n",
                  FIREBASE_FAIL_THRESHOLD, FIREBASE_PROVISION_WINDOW_MS/1000);

    startProvisionPortal(FIREBASE_PROVISION_WINDOW_MS);

    // mark provisioning window active so wifiRecoveryTick uses the forced expiry
    g_inProvWindow = true;
    g_provWindowStart = millis();

    // Clear failure counter so we don't re-trigger repeatedly
    firebaseFailCount = 0;
    firebaseLastFailAt = 0;
  }
}

// ---------------- Firestore JSON helpers (whitespace tolerant)
// Looks for: "<field>": { "stringValue": "<VALUE>" }
String fsGetStringField(const String &json, const String &field) {
  String key="\"" + field + "\"";
  int k=json.indexOf(key);
  if(k<0) return "";
  int sv=json.indexOf("\"stringValue\"",k);
  if(sv<0) {
    // fallback to first quoted string after key
    int q1=json.indexOf('"',k+key.length());
    if(q1<0) return "";
    int q2=json.indexOf('"',q1+1);
    if(q2<0) return "";
    return json.substring(q1+1,q2);
  }
  int colon=json.indexOf(':',sv); if(colon<0) return "";
  int q1=colon+1;
  while (q1 < (int)json.length() && (json[q1]==' '||json[q1]=='\n'||json[q1]=='\r'||json[q1]=='\t')) q1++;
  q1 = json.indexOf('"', q1); if(q1<0) return "";
  int q2=json.indexOf('"', q1 + 1); if(q2<0) return "";
  return json.substring(q1 + 1, q2);
}
// Looks for: "<field>": { "booleanValue": true|false }
bool fsGetBoolField(const String &json, const char *field, bool &out) {
  String key = "\"" + String(field) + "\"";
  int k = json.indexOf(key);
  if (k < 0) return false;
  int bv = json.indexOf("\"booleanValue\"", k);
  if (bv < 0) {
    // fallback: find ": true" or ": false" after field
    int colon = json.indexOf(':', k);
    if (colon < 0) return false;
    int p = colon + 1;
    while (p < (int)json.length() && (json[p]==' '||json[p]=='\n'||json[p]=='\r'||json[p]=='\t')) p++;
    if (json.startsWith("true", p))  { out = true;  return true; }
    if (json.startsWith("false", p)) { out = false; return true; }
    return false;
  }
  int colon = json.indexOf(':', bv); if (colon < 0) return false;
  int p = colon + 1;
  while (p < (int)json.length() && (json[p]==' '||json[p]=='\n'||json[p]=='\r'||json[p]=='\t')) p++;
  if (json.startsWith("true", p))  { out = true;  return true; }
  if (json.startsWith("false", p)) { out = false; return true; }
  return false;
}

// ---------------- Device registration / upserts
bool fsUpsertRootDevice() {
  if (!app.ready()) return false;
  const String docPath = "devices/" + g_mac;

  Document<Values::Value> d;
  d.add("device_id",          Values::Value(Values::StringValue(g_mac)));
  d.add("business_id",        Values::Value(Values::StringValue(g_businessId)));
  d.add("device_status",      Values::Value(Values::StringValue("online")));
  d.add("device_last_online", Values::Value(Values::TimestampValue(rfc3339NowUTC())));
  d.add("updated_at",         Values::Value(Values::TimestampValue(rfc3339NowUTC())));
  d.add("updated_by",         Values::Value(Values::StringValue(g_userEmail)));

  (void)Docs.createDocument(aClient, Firestore::Parent(g_projectId), docPath, DocumentMask(), d);
  if (aClient.lastError().code() == 0) return true;

  PatchDocumentOptions patchOpts{DocumentMask(), DocumentMask(), Precondition()};
  (void)Docs.patch(aClient, Firestore::Parent(g_projectId), docPath, patchOpts, d);
  return aClient.lastError().code() == 0;
}
bool fsUpsertBusinessDevice() {
  if (!app.ready() || g_businessId.length()==0) return false;
  const String docPath = "businessess/" + g_businessId + "/business_devices/" + g_mac;

  // CREATE (with created_at)
  Document<Values::Value> c;
  c.add("device_id",               Values::Value(Values::StringValue(g_mac)));
  c.add("device_business_id",      Values::Value(Values::StringValue(g_businessId)));
  c.add("device_status",           Values::Value(Values::BooleanValue(true)));
  c.add("device_network_ssid",     Values::Value(Values::StringValue(g_ssid)));
  c.add("device_network_password", Values::Value(Values::StringValue(g_pass)));
  c.add("device_last_online",      Values::Value(Values::TimestampValue(rfc3339NowUTC())));
  c.add("device_name",             Values::Value(Values::StringValue(g_deviceName)));
  c.add("updated_at",              Values::Value(Values::TimestampValue(rfc3339NowUTC())));
  c.add("updated_by",              Values::Value(Values::StringValue(g_userEmail)));
  c.add("created_at",              Values::Value(Values::TimestampValue(rfc3339NowUTC())));
  (void)Docs.createDocument(aClient, Firestore::Parent(g_projectId), docPath, DocumentMask(), c);
  if (aClient.lastError().code() == 0) return true;

  // PATCH (no created_at)
  Document<Values::Value> p;
  p.add("device_id",               Values::Value(Values::StringValue(g_mac)));
  p.add("device_business_id",      Values::Value(Values::StringValue(g_businessId)));
  p.add("device_status",           Values::Value(Values::BooleanValue(true)));
  p.add("device_network_ssid",     Values::Value(Values::StringValue(g_ssid)));
  p.add("device_network_password", Values::Value(Values::StringValue(g_pass)));
  p.add("device_last_online",      Values::Value(Values::TimestampValue(rfc3339NowUTC())));
  p.add("device_name",             Values::Value(Values::StringValue(g_deviceName)));
  p.add("updated_at",              Values::Value(Values::TimestampValue(rfc3339NowUTC())));
  p.add("updated_by",              Values::Value(Values::StringValue(g_userEmail)));
  PatchDocumentOptions patchOpts{DocumentMask(), DocumentMask(), Precondition()};
  (void)Docs.patch(aClient, Firestore::Parent(g_projectId), docPath, patchOpts, p);
  return aClient.lastError().code() == 0;
}
bool fsRegisterOrUpdateDevice() {
  bool ok1 = fsUpsertRootDevice();
  bool ok2 = (g_businessId.length()==0) ? true : fsUpsertBusinessDevice();
  return ok1 && ok2;
}

// ---------------- Activity flag (read device_status from business_devices)
bool readActivityCache() {
  String s = readFile(FILE_ACTIVITY);
  if (s == "0") { g_activityEnabled = false; return true; }
  if (s == "1") { g_activityEnabled = true;  return true; }
  return false;
}
void writeActivityCache(bool on) { writeFile(FILE_ACTIVITY, on ? "1" : "0"); }

// NOTE: you asked to read device_status (not activity_status). Using device_status from business_devices doc.
bool fsFetchActivityStatus(bool &activeOut) {
  activeOut = true;
  if (!app.ready() || g_businessId.length() == 0) return false;
  String docPath = "businessess/" + g_businessId + "/business_devices/" + g_mac;
  String payload = Docs.get(aClient, Firestore::Parent(g_projectId), docPath, GetDocumentOptions());
  if (aClient.lastError().code() != 0) return false;

  bool v=false;
  // try device_status first (boolean)
  if (fsGetBoolField(payload, "device_status", v)) { activeOut = v; return true; }
  // fallback to other names for compatibility
  if (fsGetBoolField(payload, "activity_status", v) ||
      fsGetBoolField(payload, "device_activity_status", v) ||
      fsGetBoolField(payload, "active", v)) {
    activeOut = v;
    return true;
  }
  return false;
}

void applyActivityRelay() {
  // g_activityEnabled == true  -> normal mode: locked
  // g_activityEnabled == false -> held unlocked
  digitalWrite(RELAY, g_activityEnabled ? RELAY_LOCKED_STATE : RELAY_UNLOCKED_STATE);
}

// ---------------- Card cache & fetch (unchanged)
bool cacheReadLast(const String &cardId, /*out*/ bool &okOut, /*out*/ uint32_t &ageSecOut) {
  okOut = false; ageSecOut = 0;
  File f = SPIFFS.open(FILE_CARD_CACHE, "r");
  if (!f) return false;

  String lastLine;
  while (f.available()) {
    String line = f.readStringUntil('\n');
    int p = line.indexOf("\"id\":\"");
    if (p >= 0) {
      int e = line.indexOf('\"', p+6);
      if (e > p && line.substring(p+6, e) == cardId) lastLine = line;
    }
  }
  f.close();
  if (lastLine.length() == 0) return false;

  int okPos = lastLine.indexOf("\"ok\":");
  int tsPos = lastLine.indexOf("\"ts\":");
  if (okPos < 0 || tsPos < 0) return false;

  bool ok = lastLine.substring(okPos+5).startsWith("true");
  uint32_t ts = lastLine.substring(tsPos+5).toInt();
  uint32_t nowSec = time(nullptr);
  okOut = ok; ageSecOut = (nowSec > ts) ? (nowSec - ts) : 0;
  return true;
}
void cacheUpsert(const String &cardId, bool ok) {
  File f = SPIFFS.open(FILE_CARD_CACHE, "a");
  if (!f) return;
  uint32_t nowSec = time(nullptr);
  f.printf("{\"id\":\"%s\",\"ok\":%s,\"ts\":%u}\n", cardId.c_str(), ok ? "true" : "false", nowSec);
  f.close();
}
bool fsFetchCardStatus(const String &businessId, const String &cardId, /*out*/ bool &statusOut) {
  if (!app.ready() || businessId.length()==0) return false;
  String docPath = "businessess/" + businessId + "/cards/" + cardId;
  String payload = Docs.get(aClient, Firestore::Parent(g_projectId), docPath, GetDocumentOptions());
  if (aClient.lastError().code() != 0) return false;

  bool v=false;
  if (fsGetBoolField(payload, "card_status", v)) { statusOut = v; return true; }
  statusOut = false; return true; // missing -> treat as denied (but still log)
}
bool cardStatusCacheFirst(const String &cardId, /*out*/ bool &status) {
  bool found=false, cachedOK=false; uint32_t ageSec=0;
  found = cacheReadLast(cardId, cachedOK, ageSec);

  if (found && ageSec <= CARD_CACHE_TTL_SEC) { status = cachedOK; return true; }

  if (WiFi.status() == WL_CONNECTED && app.ready() && g_businessId.length()) {
    bool fresh=false;
    if (fsFetchCardStatus(g_businessId, cardId, fresh)) {
      cacheUpsert(cardId, fresh);
      status = fresh;
      return true;
    }
  }

  if (found) { status = cachedOK; return true; } // stale fallback
  status = false; return true;                   // miss+offline/unknown -> deny-on-entry
}

// ---------------- Access logs helpers (device name + card meta)
String fsGetDeviceName(const String &businessId, const String &mac) {
  // Return configured device name as default if DB access fails
  if (!app.ready() || businessId.length()==0) 
    return g_deviceName.length() ? g_deviceName : String("Main Gate");
  String docPath = "businessess/" + businessId + "/business_devices/" + mac;
  String payload = Docs.get(aClient, Firestore::Parent(g_projectId), docPath, GetDocumentOptions());
  if (aClient.lastError().code() != 0) 
    return g_deviceName.length() ? g_deviceName : String("Main Gate");
  String n = fsGetStringField(payload, "device_name");
  return n.length() ? n : (g_deviceName.length() ? g_deviceName : String("Main Gate"));
}
void fsGetCardMeta(const String &businessId, const String &cardId, String &entityId, String &entityType) {
  entityId = ""; entityType = "";
  if (!app.ready() || businessId.length() == 0) return;

  String docPath = "businessess/" + businessId + "/cards/" + cardId;
  String payload = Docs.get(aClient, Firestore::Parent(g_projectId), docPath, GetDocumentOptions());
  if (aClient.lastError().code() != 0) return;

  entityId   = fsGetStringField(payload, "card_assigned_to");
  entityType = fsGetStringField(payload, "card_assigned_type");

  // Fallbacks for schema variants
  if (entityId == "")   entityId   = fsGetStringField(payload, "entity_id");
  if (entityType == "") entityType = fsGetStringField(payload, "card_assigned_to_type");
  if (entityType == "") entityType = fsGetStringField(payload, "entity_type");
}

// ---------------- Access logs: sequential LOG_N (with collision check)
uint32_t readLogCounter() { String s = readFile(FILE_LOG_COUNTER); return s.length() ? (uint32_t)s.toInt() : 0; }
void     writeLogCounter(uint32_t n) { writeFile(FILE_LOG_COUNTER, String(n)); }

// Let Firestore auto-generate document IDs for access logs
bool tryCreateAccessLogDocAuto(const String &parentCollectionPath,
                               const Document<Values::Value> &doc,
                               /*out*/ String &createdDocPayload) {
  createdDocPayload = "";

  // Create document without specifying an ID
  String payload = Docs.createDocument(aClient, Firestore::Parent(g_projectId),
                                       parentCollectionPath,
                                       DocumentMask(),
                                       (Document<Values::Value>&)doc);
  int err = aClient.lastError().code();

  if (err == 0) {
    // Success — Firestore generated a random ID
    createdDocPayload = payload;
    return true;
  }

  Serial.printf("Create LOG (auto-id) transport error: %s\n",
                aClient.lastError().message().c_str());
  return false;
}

bool fsCreateAccessLogAuto(const String &businessId,
                           const String &cardHex,
                           bool granted,
                           const String &logType) {
  if (!app.ready() || businessId.length() == 0) return false;

  String entityId, entityType;
  fsGetCardMeta(businessId, cardHex, entityId, entityType);
  String devName = fsGetDeviceName(businessId, g_mac);

  Document<Values::Value> log;
  log.add("log_business_id", Values::Value(Values::StringValue(businessId)));
  log.add("log_card_data",   Values::Value(Values::StringValue(cardHex)));
  log.add("log_device_id",   Values::Value(Values::StringValue(g_mac)));
  log.add("log_device_name", Values::Value(Values::StringValue(devName)));
  log.add("log_entity_id",   Values::Value(Values::StringValue(entityId)));
  log.add("log_entity_type", Values::Value(Values::StringValue(entityType)));
  log.add("log_status",      Values::Value(Values::StringValue(granted ? "granted" : "denied")));
  log.add("log_timestamp",   Values::Value(Values::TimestampValue(rfc3339NowUTC())));
  log.add("log_type",        Values::Value(Values::StringValue(logType)));

  // Create under collection; Firestore will auto-generate ID
  String collectionPath = "businessess/" + businessId + "/access_logs";

  String createdPayload;
  bool ok = tryCreateAccessLogDocAuto(collectionPath, log, createdPayload);
  if (ok) {
    return true; // Success
  }
  return false; // Failure -> queue stays
}

void loadAccessListFromFile() {
  if (!fileExists(FILE_ACCESS_LIST)) {
    Serial.println("No access_list.json found on SPIFFS.");
    return;
  }

  String data = readFile(FILE_ACCESS_LIST);
  if (data.length() == 0) {
    Serial.println("access_list.json empty.");
    return;
  }

  std::vector<ActiveCardEntry> newList;
  int pos = 0;
  while (pos < (int)data.length()) {
    int cdKey = data.indexOf("\"card_data\"", pos);
    if (cdKey < 0) break;

    int vq1 = data.indexOf('"', cdKey + 11);
    vq1 = data.indexOf('"', vq1 + 1);
    int vq2 = data.indexOf('"', vq1 + 1);
    if (vq1 < 0 || vq2 < 0) break;
    String card = data.substring(vq1 + 1, vq2);

    String st = "00:00";
    int stKey = data.indexOf("\"start_time\"", cdKey);
    if (stKey >= 0) {
      int a = data.indexOf('"', stKey + 12);
      a = data.indexOf('"', a + 1);
      int b = data.indexOf('"', a + 1);
      if (a >= 0 && b > a) st = data.substring(a + 1, b);
    }

    String et = "23:59";
    int etKey = data.indexOf("\"end_time\"", cdKey);
    if (etKey >= 0) {
      int a = data.indexOf('"', etKey + 10);
      a = data.indexOf('"', a + 1);
      int b = data.indexOf('"', a + 1);
      if (a >= 0 && b > a) et = data.substring(a + 1, b);
    }

    ActiveCardEntry e;
    e.card_data = card;
    e.start_time = st;
    e.end_time = et;
    newList.push_back(e);

    pos = vq2 + 1;
    if (newList.size() >= MAX_ACTIVE_CARDS) break;
  }

  portENTER_CRITICAL(&g_activeCardsMux);
  g_activeCards.clear();
  g_activeSet.clear();

  for (auto &e : newList) {
    g_activeCards.push_back(e);
    // store normalized uppercase hex
    String norm = normalizeUidStr(e.card_data);
    if (norm.length()) {
      std::string s(norm.c_str());
      g_activeSet.insert(s);  // case-insensitive match simplified by normalization
    }
  }
  portEXIT_CRITICAL(&g_activeCardsMux);

  Serial.printf("Loaded %u active cards from %s\n", (unsigned)g_activeCards.size(), FILE_ACCESS_LIST);
}

// ---------------- Access logs: local queue (process-first-N, keep rest)
void queueAccessLog(const String &businessId, const String &cardId, bool granted, const String &logType) {
  // Append a compact JSON line; upload is skipped until config complete.
  String s = "{";
  s += "\"bid\":\"" + businessId + "\","; 
  s += "\"card\":\"" + cardId + "\","; 
  s += "\"granted\":" + String(granted ? "true" : "false") + ","; 
  s += "\"type\":\"" + logType + "\"";
  s += "}";
  appendLine(FILE_LOG_QUEUE, s);
}

void flushQueueBatch(size_t maxLines = 50) {
  if (!(WiFi.status() == WL_CONNECTED && app.ready() && g_businessId.length())) return;
  File src = SPIFFS.open(FILE_LOG_QUEUE, "r");
  if (!src) return;

  Serial.println("Flushing access_logs queue...");
  String keep = "";
  size_t processed = 0;
  int sent = 0;

  while (src.available()) {
    String line = src.readStringUntil('\n');
    line.trim();
    if (line.length() == 0) continue;

    if (processed < maxLines) {
      String bid = jsonGetStr(line, "bid");
      String cid = jsonGetStr(line, "card");
      String type = jsonGetStr(line, "type");
      bool granted = (line.indexOf("\"granted\":true") >= 0);

      // If queued without BID (pre-provision), use current config BID if available; else keep.
      String effectiveBID = (bid.length() ? bid : g_businessId);
      if (effectiveBID.length() == 0) {
        keep += line + "\n"; // still not configured; keep it
      } else {
        bool ok = fsCreateAccessLogAuto(effectiveBID, cid, granted, type);
        if (ok) sent++;
        else    keep += line + "\n";
      }
      processed++;
    } else {
      keep += line + "\n";          // keep unprocessed lines
    }
  }
  src.close();
  writeFile(FILE_LOG_QUEUE, keep);
  Serial.printf("Flushed %d/%d logs.\n", sent, (int)processed);
}

void flushQueueIfNeeded() {
  if (millis() - g_lastFlush > FLUSH_INTERVAL_MS || fsUsage() >= FLUSH_FS_THRESH) {
    flushQueueBatch(50);
    g_lastFlush = millis();
  }
}

// ---------------- Relay + heartbeat + RFID helpers
void relayGrantPulse() {
  // Temporarily unlock (LOW), hold for DOOR_PULSE_MS, then re-lock (HIGH).
  digitalWrite(RELAY, RELAY_UNLOCKED_STATE);
  delay(DOOR_PULSE_MS);
  digitalWrite(RELAY, RELAY_LOCKED_STATE);
}

void heartbeat(bool immediate=false) {
  if (!immediate && millis() - g_lastHeartbeat < HEARTBEAT_MS) return;
  if (WiFi.status() == WL_CONNECTED && app.ready()) {
    (void)fsRegisterOrUpdateDevice();  // upsert both device docs
    bool act=false;
    if (fsFetchActivityStatus(act)) {
      g_activityEnabled = act;
      writeActivityCache(act);
      applyActivityRelay();
      Serial.printf("Heartbeat: device_status=%s\n", g_activityEnabled ? "ON" : "OFF");
    }
    // IMPORTANT: fetch active cards every heartbeat? No — only fetch when remote updated_at changed.
    // We still call fetchActiveCardsFromFirebase_v2() here if you want periodic refresh; commented out:
    // fetchActiveCardsFromFirebase_v2();
  }
  g_lastHeartbeat = millis();
}

// Read UID from a reader and return canonical uppercase hex (no spaces)
// Supports up to UID_MAX_BYTES bytes
String readUidHexFrom(MFRC522 &r) {
  if (!r.PICC_IsNewCardPresent()) return "";
  if (!r.PICC_ReadCardSerial())   return "";
  // Each byte -> 2 hex chars + null. Use temporary small buffer for formatting.
  char buf[8]; // enough for "%02X" + null
  String out;
  for (byte i = 0; i < r.uid.size && i < UID_MAX_BYTES; i++) {
    sprintf(buf, "%02X", r.uid.uidByte[i]);
    out += buf;
  }
  r.PICC_HaltA();
  return normalizeUidStr(out);
}

// ---------------- Wi-Fi + recovery logic
void WiFiEventCB(WiFiEvent_t event) {
  unsigned long now = millis();

  if (event == ARDUINO_EVENT_WIFI_STA_DISCONNECTED) {
    Serial.println("WiFi disconnected (event) — starting recovery timer");
    if (g_wifiFailStart == 0) g_wifiFailStart = now;
  }
  else if (event == ARDUINO_EVENT_WIFI_STA_GOT_IP) {
    Serial.printf("WiFi IP: %s RSSI=%d\n", WiFi.localIP().toString().c_str(), (int)WiFi.RSSI());

    // Reset the wifi lookup state now that we have an IP
    g_wifiFailStart = 0;

    // Record GOT_IP time and request init from loop after a short settle
    g_gotIpAt = millis();
    Serial.printf("GOT_IP: scheduling Firebase init in %lums.\n", GOT_IP_INIT_DELAY_MS);

    // If portal active and forced, we'll let firebaseInitPoll() / loop determine whether to close portal.
    if (g_portalActive && g_forcedProvUntil != 0) {
      Serial.printf("Portal active (forced until +%lus). Will re-evaluate once Firebase responds.\n",
                    (unsigned long)((g_forcedProvUntil - millis())/1000));
    }
  }
}

// returns true if connected within a short attempt (~10s)
bool wifiConnect() {
  WiFi.persistent(false);
  WiFi.setAutoReconnect(true);      // let the driver handle reconnects automatically
  WiFi.onEvent(WiFiEventCB);        // register the event callback

  Serial.printf("WiFi: connecting to %s", g_ssid.c_str());
  WiFi.begin(g_ssid.c_str(), g_pass.c_str());

  int tries = 0;
  while (WiFi.status() != WL_CONNECTED && tries++ < 20) { // ~10s blocking initial attempt
    delay(500);
    Serial.print('.');
  }

  if (WiFi.status() == WL_CONNECTED) {
    Serial.println(" connected");
    g_wifiFailStart = 0;
    return true;
  }

  Serial.println(" failed");
  // start the recovery timer if not already
  if (g_wifiFailStart == 0) g_wifiFailStart = millis();
  return false;
}

void wifiRecoveryTick() {
  unsigned long now = millis();

  // --- If Wi-Fi is connected ---
  if (WiFi.status() == WL_CONNECTED) {
    // If portal is active and we have a forced window that hasn't expired, keep the portal open.
    if (g_portalActive) {
      if (g_forcedProvUntil != 0 && now < g_forcedProvUntil) {
        Serial.printf("Wi-Fi connected but portal forced open until +%lus. Keeping AP.\n",
                      (unsigned long)((g_forcedProvUntil - now) / 1000));
        return;
      }

      // If portal active but no forced window, check normal provisioning window
      if (g_inProvWindow) {
        if (now - g_provWindowStart >= PROVISION_WINDOW_MS) {
          Serial.println("Normal provisioning window expired while connected — stopping portal.");
          stopProvisionPortal();
          g_inProvWindow = false;
          g_provWindowStart = 0;
        } else {
          unsigned long remain = (PROVISION_WINDOW_MS - (now - g_provWindowStart)) / 1000;
          Serial.printf("Portal active (normal) — keeping AP for another %lus.\n", remain);
          return;
        }
      } else {
        // No inProvWindow and no forced window -> safe to stop
        stopProvisionPortal();
        g_forcedProvUntil = 0;
      }
    }

    // Reset lookup/recovery timers now that we have an IP
    g_wifiFailStart = 0;
    g_provWindowStart = 0;
    g_inProvWindow = false;
    return;
  }

  // --- Not connected ---
  if (g_wifiFailStart == 0) {
    // start tracking lookup period
    g_wifiFailStart = now;
    Serial.println("Wi-Fi not connected — starting lookup timer.");
  }

  // If currently in provisioning window (user-initiated or forced), check end conditions
  if (g_inProvWindow) {
    // If a forced-until timestamp exists, use that expiry.
    if (g_forcedProvUntil != 0) {
      if (now >= g_forcedProvUntil) {
        Serial.println("Forced provisioning window ended — closing AP and resuming Wi-Fi driver attempts");
        stopProvisionPortal();
        g_inProvWindow = false;
        g_provWindowStart = 0;
        g_forcedProvUntil = 0;
        // restart lookup timer so the driver gets another full lookup window
        g_wifiFailStart = now;
      } else {
        // still forced; keep portal
        return;
      }
    } else {
      // Normal provisioning window expiry (PROVISION_WINDOW_MS)
      if (now - g_provWindowStart >= PROVISION_WINDOW_MS) {
        Serial.println("Provisioning window ended — closing AP and resuming Wi-Fi driver attempts");
        stopProvisionPortal();
        g_inProvWindow = false;
        g_provWindowStart = 0;
        // restart lookup timer so the driver gets another full lookup window
        g_wifiFailStart = now;
      } else {
        // still in normal provisioning window
        return;
      }
    }
    return;
  }

  // Not in provisioning window: are we still within the configured "search for wifi" timeout?
  unsigned long elapsed = now - g_wifiFailStart;
  if (elapsed < WIFI_LOOKUP_TIMEOUT_MS) {
    static unsigned long lastLog = 0;
    if (now - lastLog >= 60000UL) { // log every minute
      Serial.printf("Wi-Fi still disconnected (elapsed %lus) — driver auto-retry active\n", elapsed / 1000);
      lastLog = now;
    }
    return;
  }

  // Lookup timeout expired -> open provisioning portal (normal case)
  if (!g_inProvWindow) {
    Serial.println("Wi-Fi not restored after lookup timeout — starting provisioning portal for a short window");
    // Normal start: don't mark as forced. startProvisionPortal() will set g_inProvWindow/g_provWindowStart.
    startProvisionPortal(false);
    // Reset Wi-Fi lookup timer so after the provisioning window we get a fresh lookup window
    g_wifiFailStart = now;
  }
}

// Polling-based, non-blocking runtime reset handler.
// Call runtimeResetTick() at the very start of loop(). 
void runtimeResetTick() {
  int val = digitalRead(FACTORY_RESET_PIN); // HIGH = pressed for active-HIGH module
  unsigned long now = millis();

  static unsigned long pressStart = 0;   // timestamp when press began
  static bool pressed = false;           // are we currently seeing the button pressed?

  // Press started
  if (val == HIGH && !pressed) {
    pressed = true;
    pressStart = now;
    Serial.println("Reset press detected.");
    return;
  }

  // Still being held - do nothing here (we handle action on RELEASE)
  if (val == HIGH && pressed) {
    return;
  }

  // Button released (or not pressed)
  if (val == LOW && pressed) {
    unsigned long held = (now >= pressStart) ? (now - pressStart) : 0;
    pressed = false;
    pressStart = 0;

    // Short press: >=1s but <5s -> perform normal restart (no file changes)
    if (held >= RESET_SHORT_MS && held < RESET_LONG_MS) {
      Serial.printf("Reset released after %lums: performing short restart (no config removed).\n", held);
      delay(100); // settle
      ESP.restart();
      return; // device will restart
    }

    // Long press: >=5s -> perform safe factory reset (remove config.json)
    if (held >= RESET_LONG_MS) {
      Serial.printf("Reset released after %lums: performing long reset (remove config).\n", held);

      // Remove only config.json (safe)
      if (SPIFFS.exists(FILE_CONFIG)) {
        SPIFFS.remove(FILE_CONFIG);
        Serial.println("Removed " + String(FILE_CONFIG));
      } else {
        Serial.println("No config found to remove.");
      }

      // Technician full-wipe if tech pin shorted to GND
      if (FACTORY_RESET_FULL_PIN >= 0 && digitalRead(FACTORY_RESET_FULL_PIN) == LOW) {
        Serial.println("Technician full-wipe requested — removing logs and caches...");
        if (SPIFFS.exists(FILE_LOG_QUEUE))   { SPIFFS.remove(FILE_LOG_QUEUE);   Serial.println(" - removed " + String(FILE_LOG_QUEUE)); }
        if (SPIFFS.exists(FILE_LOG_COUNTER)) { SPIFFS.remove(FILE_LOG_COUNTER); Serial.println(" - removed " + String(FILE_LOG_COUNTER)); }
        if (SPIFFS.exists(FILE_ACTIVITY))    { SPIFFS.remove(FILE_ACTIVITY);    Serial.println(" - removed " + String(FILE_ACTIVITY)); }
        if (SPIFFS.exists(FILE_CARD_CACHE))  { SPIFFS.remove(FILE_CARD_CACHE);  Serial.println(" - removed " + String(FILE_CARD_CACHE)); }
        if (SPIFFS.exists(FILE_ACCESS_LIST)) { SPIFFS.remove(FILE_ACCESS_LIST); Serial.println(" - removed " + String(FILE_ACCESS_LIST)); }
        if (SPIFFS.exists(FILE_ACCESS_META)) { SPIFFS.remove(FILE_ACCESS_META); Serial.println(" - removed " + String(FILE_ACCESS_META)); }
        Serial.println("Technician full-wipe complete.");
      } else {
        Serial.println("Technician full-wipe not requested; logs preserved.");
      }

      delay(150);
      Serial.println("Restarting device...");
      ESP.restart();
      return;
    }

    // Held for less than short threshold -> ignore (bounce)
    if (held < RESET_SHORT_MS) {
      Serial.printf("Reset press too short (%lums) — ignored.\n", held);
    }
  }
}

// ---------------- Setup / Loop
void setup() {
  Serial.begin(115200);

  // Mount SPIFFS before any file operations (factory reset checks need SPIFFS available)
  fsEnsure();
  Serial.printf("Booting... heap=%u\n", (unsigned)ESP.getFreeHeap());
  Serial.printf("Flash size map: used=%u total=%u\n", (unsigned)SPIFFS.usedBytes(), (unsigned)SPIFFS.totalBytes());


  // Configure reset pins early so runtime reset works no matter what happens later
  pinMode(FACTORY_RESET_PIN, INPUT_PULLDOWN); // For active-HIGH touch button: ensure pin idles LOW
  if (FACTORY_RESET_FULL_PIN >= 0) pinMode(FACTORY_RESET_FULL_PIN, INPUT_PULLUP); // tech jumper defaults HIGH

  pinMode(RELAY, OUTPUT);
  digitalWrite(RELAY, RELAY_LOCKED_STATE); // start locked

  loadConfigIfPresent();     // load saved config (if exists)
  // Load previously saved active_cards into RAM at boot (if present)
  loadAccessListFromFile();

  // debug: show loaded config values (mask password)
  Serial.println("=== LOADED CONFIG ===");
  Serial.printf("ssid: '%s'\n", g_ssid.c_str());
  Serial.printf("pass length: %d\n", (int)g_pass.length()); // we don't print raw password
  Serial.printf("api_key: '%s'\n", g_apiKey.c_str());
  Serial.printf("project_id: '%s'\n", g_projectId.c_str());
  Serial.printf("user_email: '%s'\n", g_userEmail.c_str());
  Serial.printf("user_pass length: %d\n", (int)g_userPass.length());
  Serial.printf("business_id: '%s'\n", g_businessId.c_str());
  Serial.printf("device_name: '%s'\n", g_deviceName.c_str());
  Serial.println("=======================");

  // RFID bring-up
  SPI.begin();
  rfidEntry.PCD_Init(MFRC522_ENTRY_SS, MFRC522_ENTRY_RST);
  rfidExit .PCD_Init(MFRC522_EXIT_SS, MFRC522_EXIT_RST);
  Serial.println("MFRC522 (entry & exit) ready. Tap a card...");

  // unique MAC-based ID
  uint64_t efuse = ESP.getEfuseMac(); // 48-bit factory ID
  char devId[18];
  sprintf(devId, "%02X:%02X:%02X:%02X:%02X:%02X",
          (uint8_t)(efuse >> 40), (uint8_t)(efuse >> 32), (uint8_t)(efuse >> 24),
          (uint8_t)(efuse >> 16), (uint8_t)(efuse >> 8),  (uint8_t)(efuse));
  g_mac = devId;
  Serial.print("Device ID: "); Serial.println(g_mac);

  // === CONFIG / PROVISIONING DECISION ===
  if (!configComplete()) {
    // no config.json or incomplete → start setup AP (normal window)
    startProvisionPortal(0); // 0 = normal (non-forced) window
  } else {
    // try Wi-Fi first
    if (!wifiConnect()) {
      Serial.println("WiFi connect failed — starting provisioning portal for reconfiguration.");
      // operator should fix network: keep portal open for the full forced window
      startProvisionPortal(FIREBASE_PROVISION_WINDOW_MS);
    } else {
      // got IP → sync time & init Firebase
      timeSync();
      firebaseInitStart();

      Serial.printf("WiFi.status() = %d\n", WiFi.status());
      if (WiFi.status() == WL_CONNECTED) {
        Serial.printf("Connected: IP=%s RSSI=%d\n", WiFi.localIP().toString().c_str(), (int)WiFi.RSSI());
      } else {
        Serial.println("WiFi failed to connect with provided credentials.");
      }

      if (!app.ready()) {
        Serial.println("Firebase init failed — opening provisioning portal to reconfigure credentials.");
        // Force the portal for FIREBASE_PROVISION_WINDOW_MS so it stays open and operator can fix credentials.
        startProvisionPortal(FIREBASE_PROVISION_WINDOW_MS);
      } else {
        // Firebase ready → normal operation
        fsRegisterOrUpdateDevice();

        // Load device_status flag (server or cache) — using device_status now
        bool v = false;
        if (fsFetchActivityStatus(v)) {
          g_activityEnabled = v;
          writeActivityCache(v);
        } else if (!readActivityCache()) {
          g_activityEnabled = true;
          writeActivityCache(true);
        }
        applyActivityRelay();

        // Flush any queued logs
        flushQueueBatch(100);

        g_lastHeartbeat = millis();
        g_lastFlush     = millis();

        // Fetch active cards now
        fetchActiveCardsFromFirebase_v2();
      }
    }
  }
}

void loop() {
  // runtime reset should be checked first so operator can always trigger reprovision
  runtimeResetTick();

  // Check Firebase failures -> may trigger forced AP
  checkFirebaseFailureState();

  // Wi-Fi recovery state machine (may open provisioning window)
  wifiRecoveryTick();

  // If portal active, serve it immediately (important to do this early)
  if (g_portalActive) portal.handleClient();

  // Decide whether to start Firebase init:
  {
    unsigned long now = millis();

    // Preferred: start after GOT_IP settle delay and after any backoff window.
    if (!g_firebaseInitInProgress && !app.ready() && g_gotIpAt != 0) {
      if ((now - g_gotIpAt) >= GOT_IP_INIT_DELAY_MS && now >= g_nextFirebaseInitAttempt) {
        if (WiFi.status() == WL_CONNECTED) {
          Serial.println("Main loop: starting Firebase init (post-GOT_IP settle).");
          firebaseInitStart();
          g_gotIpAt = 0;
        } else {
          Serial.println("Main loop: GOT_IP settle passed but WiFi not connected; deferring firebase init.");
          g_gotIpAt = 0;
        }
      }
    }
    else if (g_requestFirebaseInit) {
      g_requestFirebaseInit = false;
      if (!g_firebaseInitInProgress && !app.ready() && now >= g_nextFirebaseInitAttempt) {
        Serial.println("Main loop: starting Firebase init as requested by event (fallback).");
        firebaseInitStart();
      } else {
        Serial.println("Main loop: firebase already initializing or ready; skipping start.");
      }
    }
  }

  // Non-blocking firebase poll / initialization
  firebaseInitPoll();

  // Let SDK do a light loop as well (small, non-blocking)
  if (!g_firebaseInitInProgress) {
    app.loop();
    Docs.loop();
  }

  // periodic tasks
  heartbeat();          // hourly device upsert + device_status refresh
  flushQueueIfNeeded(); // hourly or when SPIFFS >= threshold

  // ---------- RFID ENTRY ----------
  String uid = readUidHexFrom(rfidEntry);
  if (uid.length()) {
    bool grant = false;
    String nowHM = currentHHMM();

    // Normalize once and use normalized value for set lookup
    String uidNorm = normalizeUidStr(uid);
    std::string uid_s(uidNorm.c_str());
    bool foundInSet = (g_activeSet.find(uid_s) != g_activeSet.end());

    if (foundInSet) {
      // If device is disabled, deny — must follow global device_status
      if (!g_activityEnabled) {
        grant = false;
      } else {
        // Check shift timing validity using normalized lookup across all shifts
        String st, et;
        if (findActiveCardTimes(uidNorm, nowHM, st, et)) {
          // matched a shift containing current time
          grant = true;
        } else {
          // either no shift, or shifts exist but none match current time
          // log diagnostics: show first matching entry (if any) and up to 8 raw matches
          Serial.printf("ENTRY: UID present but no matching shift for nowHM=%s; showing first matching entry (if present)\n", nowHM.c_str());
          int printed = 0;
          for (auto &e : g_activeCards) {
            if (printed >= 8) break;
            if (normalizeUidStr(e.card_data) == uidNorm) {
              Serial.printf("  candidate shift: start=%s end=%s raw='%s'\n", e.start_time.c_str(), e.end_time.c_str(), e.card_data.c_str());
              printed++;
            }
          }
          grant = false;
        }
      }
    } else {
      // not found in active_cards -> diagnostic info
      bool foundCI = false;
      for (auto &e : g_activeCards) {
        if (e.card_data.equalsIgnoreCase(uid)) { foundCI = true; break; }
      }
      Serial.printf("ENTRY lookup: raw='%s' norm='%s' set_size=%u found=%d case_insensitive=%d\n",
                    uid.c_str(), uidNorm.c_str(), (unsigned)g_activeSet.size(),
                    foundInSet ? 1 : 0, foundCI ? 1 : 0);

      // Print snapshot of set for debugging (first up to 8 entries)
      if (g_activeSet.size() > 0 && !foundCI) {
        Serial.println("ActiveSet snapshot (first 8 entries):");
        int i=0;
        for (const auto &x : g_activeSet) {
          Serial.printf("  %s\n", x.c_str());
          if (++i >= 8) break;
        }
      }
      grant = false;
    }

    // Relay pulse only if granted and device active
    if (grant && g_activityEnabled) relayGrantPulse();

    queueAccessLog(g_businessId, uid, grant, "entry");
    Serial.printf("ENTRY %s  card=%s  at=%s  (device_status=%s)\n",
      grant ? "granted" : "denied",
      uid.c_str(), rfc3339NowUTC().c_str(),
      g_activityEnabled ? "ON" : "OFF");
  }

  // ---------- RFID EXIT ----------
  String uid2 = readUidHexFrom(rfidExit);
  if (uid2.length()) {
    bool grant = false;

    // Normalize scanned UID for lookup
    String uid2Norm = normalizeUidStr(uid2);
    std::string uid2_s(uid2Norm.c_str());
    bool foundInSet = (g_activeSet.find(uid2_s) != g_activeSet.end());

    // EXIT should allow if card is active; device_status doesn't block EXIT
    if (foundInSet) {
      grant = true;
    } else {
      // Diagnostic info to help find mismatches
      bool foundCI = false;
      for (auto &e : g_activeCards) {
        if (e.card_data.equalsIgnoreCase(uid2)) { foundCI = true; break; }
      }
      Serial.printf("EXIT lookup: raw='%s' norm='%s' set_size=%u found=%d case_insensitive=%d\n",
                    uid2.c_str(), uid2Norm.c_str(), (unsigned)g_activeSet.size(),
                    foundInSet ? 1 : 0, foundCI ? 1 : 0);

      if (g_activeSet.size() > 0 && !foundCI) {
        Serial.println("ActiveSet snapshot (first 8 entries):");
        int i=0;
        for (const auto &x : g_activeSet) {
          Serial.printf("  %s\n", x.c_str());
          if (++i >= 8) break;
        }
      }

      grant = false;
    }

    if (grant) relayGrantPulse();

    queueAccessLog(g_businessId, uid2, grant, "exit");
    Serial.printf("EXIT %s  card=%s  at=%s  (device_status=%s)\n",
      grant ? "granted" : "denied",
      uid2.c_str(), rfc3339NowUTC().c_str(),
      g_activityEnabled ? "ON" : "OFF");
  }
}
