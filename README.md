# WhatsApp WAP Client

A complete WhatsApp client accessible through **WAP (Wireless Application Protocol)** for vintage mobile phones like Nokia 7210/7250i. Uses WML 1.x pages served over HTTP, designed to work through a **Kannel WAP gateway** for CSD/GPRS devices.

Built on [Baileys](https://github.com/WhiskeySockets/Baileys) (WhatsApp Web multi-device API) and Express.js.

## Features

### Messaging
- Send and receive text messages with full Unicode support
- Media support: images, videos, audio, documents, stickers
- Sticker packs based on OpenMoji (open-source, keyless)
- Audio transcription via Whisper AI (offline, no internet needed)
- Message actions: reply, forward, delete, react, mark as read
- Media downloads in multiple formats (WBMP, JPEG, PNG)

### Contacts & Chats
- Contact list with search and pagination
- Chat history with full message threading
- Recent chats on home page with last message preview
- Favorites system for quick access to frequent contacts

### Groups
- Create, join, leave groups
- Manage participants (add, remove, promote, demote)
- Group info and settings

### WAP Push Notifications
- Receive real-time **WAP Push SI** notifications on your phone when new messages arrive
- Requires a NowSMS gateway (or compatible WAP Push provider)
- All options configurable from **Settings > WAP Push** on the device:
  - **Enable/disable** WAP Push globally
  - **Expiration**: enable/disable + set expiry time (30s to 1h)
  - **Auto-delete**: automatically remove expired notifications from the device
  - **History**: enable/disable + set max notifications limit (10–100)

### Status Broadcast
- Post text, image, or video status updates
- Visible to all contacts for 24 hours

### Profile & Privacy
- Update name, status, profile picture
- Privacy settings: last seen, profile photo, read receipts, groups
- Block/unblock contacts

### Advanced
- QR code pairing (PNG, WBMP, SVG, text) or **pairing code** (phone number based)
- Full-text search across messages, contacts, chats, groups
- TTS (text-to-speech) voice messages via espeak (offline)
- RTSP video streaming for media playback
- Persistent storage with automatic data persistence
- i18n: English and Italian (easily extensible)
- HTTPS with auto Let's Encrypt certificates

### Markup Modes
- **WML** (default): WML 1.0/1.1 for WAP phones (Nokia 7210/7250i, Kannel gateway)
- **XHTML**: XHTML Mobile Profile 1.0 (WAP-277) with WCSS styling — for WAP 2.0 browsers (Nokia WAP 2.0, Opera Mini, NetFront, Openwave)
- **HTML5**: Modern HTML5 with WhatsApp-themed CSS — for desktop/mobile browsers
- Upload page has its own independent mode (`UPLOAD_MARKUP_MODE`)
- Set via `MARKUP_MODE` environment variable (`wml`, `xhtml`, `html5`)

### WAP Compatibility
- **WML mode**: WML 1.0/1.1 with ISO-8859-1 encoding for WAP 1.x devices
- **XHTML mode**: XHTML Mobile Profile 1.0 (WAP-277) with WCSS styling for WAP 2.0 devices
  - DOCTYPE: `-//WAPFORUM//DTD XHTML Mobile 1.0//EN`
  - Content-Type: `application/vnd.wap.xhtml+xml`
  - CSS2 subset only (no CSS3, no custom properties, no border-radius)
- Optimized for low memory and slow connections
- Works through Kannel WAP gateway (WSP protocol)
- Nokia 7210/7250i tested

## Requirements

- **Node.js** >= 18
- **npm**
- A WAP gateway (e.g. [Kannel](https://www.kannel.org/)) for old phones
- (Optional) NowSMS for WAP Push notifications
- (Optional) espeak for TTS voice messages
- (Optional) ffmpeg for video/audio conversion (bundled via ffmpeg-static)

## Installation

```bash
git clone https://github.com/David-cryptonite/WhatsAppWapClient.git
cd WhatsAppWapClient
npm install
cp .env.example .env   # then edit .env with your settings
```

## Configuration

All configuration is done via environment variables. You can set them in a `.env` file (recommended), in your shell, or use the provided startup scripts.

> **Important:** Never commit your `.env` file — it is already in `.gitignore`. Use `.env.example` as a template.

### Environment Variables

| Variable | Default | Description |
|---|---|---|
| `NODE_ENV` | `development` | Node environment (`development` or `production`) |
| `PORT` | `3500` | HTTP server port |
| `RTSP_PORT` | `8554` | RTSP streaming port for video playback |
| `WML_REFRESH_TIMER_UNITS` | `100` | WML timer units for auto-refresh (`100 = 10s`, `50 = 5s`) |
| `APP_DATA_DIR` | `./data` | Directory for persistent data (contacts, chats, messages) |
| `AUTH_DB_PATH` | `./auth.db` | SQLite database for user authentication |
| `SESSION_DB_PATH` | `./sessions.db` | SQLite database for Express sessions |
| `AUTH_ENABLED` | `true` | Enable/disable login requirement (`true/false/1/0/yes/no`) |
| `HTTPS_ENABLED` | `false` | Enable HTTPS with auto Let's Encrypt (`true/1/yes/on`) |
| `HTTPS_DOMAIN` | `example.com` | Domain for Let's Encrypt certificate |
| `HTTPS_EMAIL` | `admin@example.com` | Email for Let's Encrypt registration |
| `HTTPS_PORT` | `443` | HTTPS port |
| `HTTPS_CERTS_DIR` | `./certs` | Directory for TLS certificates |
| `WA_PHONE_NUMBER` | *(empty)* | WhatsApp phone number for pairing code (digits only, with country code, e.g. `391234567890`). If empty, uses QR code. |
| `MARKUP_MODE` | `wml` | Output format for pages: `wml`, `xhtml`, `html5` |
| `UPLOAD_MARKUP_MODE` | `html5` | Output format for upload page: `xhtml` or `html5` |
| `WAP_PUSH_ENABLED` | `true` | Initial default for WAP Push master switch |
| `WAP_PUSH_BASE_URL` | *(empty)* | NowSMS gateway URL for sending WAP Push SI |
| `WAP_PUSH_AUTH` | *(empty)* | Authorization header for NowSMS (`Basic base64(user:pass)`) |
| `WAP_PUSH_PHONE` | *(empty)* | Initial phone number for WAP Push notifications |
| `WAP_SERVER_BASE` | *(empty)* | Public URL of this server reachable from the phone's mobile network. **Must not be 127.0.0.1** |

### Startup Scripts

Pre-configured scripts with sensible defaults:

**Windows (PowerShell):**
```powershell
.\start-windows.ps1
```

**Linux/macOS:**
```bash
./start-linux.sh
```

Both scripts set all environment variables with defaults and then run `npm start`. Override any variable by setting it before running the script:

```bash
# Linux - disable WAP Push, use pairing code
WAP_PUSH_ENABLED=false WA_PHONE_NUMBER=391234567890 ./start-linux.sh
```

```powershell
# Windows - change port, disable auth
$env:PORT = "8080"; $env:AUTH_ENABLED = "false"; .\start-windows.ps1
```

At every startup, the app runs a background sticker sync from OpenMoji (downloads missing stickers for local packs).

### Manual Start

```bash
# Minimal (QR code, no WAP Push, auth enabled)
node serverWml.js

# With environment variables
PORT=3500 AUTH_ENABLED=false node serverWml.js
```

### Using pm2 (Production)

```bash
npm install -g pm2
pm2 start serverWml.js --name whatsapp-wap
pm2 save
pm2 startup
```

## Getting Started

### Step 1: First Launch & WhatsApp Login

When you start the server for the first time, you need to link it to your WhatsApp account. There are two methods:

#### Method A: QR Code (default)

1. Start the server: `npm start` (or use a startup script)
2. Open `http://<server-ip>:3500/wml/qr.wml` on any browser
3. Open WhatsApp on your phone > **Settings > Linked Devices > Link a Device**
4. Scan the QR code displayed on the page
5. Wait for the connection confirmation — the QR page will redirect to Home

#### Method B: Pairing Code (phone number)

1. Set `WA_PHONE_NUMBER` to your full number with country code (e.g. `391234567890` for Italy +39):
   ```bash
   # In .env file
   WA_PHONE_NUMBER=391234567890

   # Or via command line
   WA_PHONE_NUMBER=391234567890 npm start
   ```
2. Start the server
3. Open `http://<server-ip>:3500/wml/qr.wml` — it will show a **6-digit pairing code**
4. Open WhatsApp on your phone > **Settings > Linked Devices > Link a Device > Link with phone number**
5. Enter the 6-digit code shown on the page
6. Wait for confirmation

> **Note:** After the first successful pairing, the session is saved in `auth_info_baileys/`. You won't need to pair again unless you log out from WhatsApp or delete the session folder.

### Step 2: App Login (Authentication)

If `AUTH_ENABLED=true` (default), the app requires a username and password to access.

- **First run:** The server creates a default account:
  - Username: `admin`
  - Password: `admin`
- **Change the password** immediately from **Settings > Change Password** on the device
- To **disable authentication** (e.g. for local/single-user setups): set `AUTH_ENABLED=false`

### Step 3: Browse on Your Device

- **WAP phone (Nokia 7210, etc.):** Set up your Kannel WAP gateway to proxy to this server, then navigate to the home page via WAP
- **WAP 2.0 phone (with XHTML browser):** Set `MARKUP_MODE=xhtml` and open `http://<server-ip>:3500/wml/home.wml` directly
- **Modern browser:** Set `MARKUP_MODE=html5` and open `http://<server-ip>:3500/wml/home.wml`

### WAP Gateway Setup (Kannel)

For old phones without a web browser, you need a WAP gateway like Kannel that translates HTTP/WML into WSP (WAP Session Protocol) over CSD or GPRS bearers.

Point your phone's WAP settings to the Kannel gateway IP, and configure Kannel to proxy requests to this server.

**Note:** Kannel's WSP layer does not support HTTP cookies properly. A URL-based session fallback is planned for future releases.

### WAP Push Notifications (Optional)

When a new WhatsApp message arrives, the server can send a WAP Push SI (Service Indication) notification to the configured phone number via NowSMS.

**Setup:**
1. Install and configure a [NowSMS](https://www.nowsms.com/) gateway
2. Set the following environment variables in your `.env`:
   ```env
   WAP_PUSH_ENABLED=true
   WAP_PUSH_BASE_URL=http://your-nowsms-server:port/Send%20WAP%20Push%20Message.htm
   WAP_PUSH_AUTH=Basic <base64-encoded-user:pass>
   WAP_PUSH_PHONE=your-phone-number
   WAP_SERVER_BASE=http://your-public-ip:3500
   ```
3. You can also configure all options at runtime from the phone in **Settings > WAP Push**

The notification includes the sender name, message preview, and a direct link to the chat.

Environment variables (`WAP_PUSH_ENABLED`, `WAP_PUSH_PHONE`) set the initial defaults; runtime settings override them and are persisted across restarts.

## Project Structure

```
WhatsAppWapClient/
  serverWml.js          # Main server (Express + Baileys + WML generation)
  persistentStorage.js  # Async JSON file persistence
  loadChatUtils.js      # Chat loading utilities
  locales/
    en.json             # English translations
    it.json             # Italian translations
  stickers/             # Downloaded sticker packs (auto-generated)
  data/                 # Persistent data (contacts, chats, messages, settings)
  auth_info_baileys/    # WhatsApp auth state (multi-device)
  media_cache/          # Cached media files
  start-windows.ps1     # Windows startup script
  start-linux.sh        # Linux/macOS startup script
  .env.example          # Example environment variables
```

## Internationalization (i18n)

The app supports multiple languages. Currently available:
- **English** (`en`)
- **Italian** (`it`)

Change language from the phone: **Settings > UI Language**.

To add a new language, copy `locales/en.json`, translate all values, and save as `locales/<code>.json`.

## License

ISC
