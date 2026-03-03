# ============================================================
# WhatsApp WAP Client - Windows Startup Script
# ============================================================
# Sets all environment variables with sensible defaults and
# starts the Node.js server via npm start.
#
# Usage:
#   .\start-windows.ps1                              # uses all defaults
#   $env:PORT = "8080"; .\start-windows.ps1           # override port
#   $env:WA_PHONE_NUMBER = "393401234567"; .\start-windows.ps1  # pairing code
#   $env:WAP_PUSH_ENABLED = "false"; .\start-windows.ps1       # disable push
#
# All variables use "if not already set" logic, so you can
# override any value by setting it before running this script.
# ============================================================

$ErrorActionPreference = "Stop"

# ---------- Server ----------
# NODE_ENV: "development" or "production" (affects logging verbosity)
if ([string]::IsNullOrWhiteSpace($env:NODE_ENV)) { $env:NODE_ENV = "development" }
# PORT: HTTP port the WML server listens on
if ([string]::IsNullOrWhiteSpace($env:PORT)) { $env:PORT = "3500" }
# RTSP_PORT: RTSP streaming port for video playback on WAP devices
if ([string]::IsNullOrWhiteSpace($env:RTSP_PORT)) { $env:RTSP_PORT = "8554" }
# WML_REFRESH_TIMER_UNITS: WML timer units (1 unit = 0.1s). 100 = 10 seconds
if ([string]::IsNullOrWhiteSpace($env:WML_REFRESH_TIMER_UNITS)) { $env:WML_REFRESH_TIMER_UNITS = "100" }
# APP_DATA_DIR: directory for persistent JSON data (contacts, chats, messages, settings)
if ([string]::IsNullOrWhiteSpace($env:APP_DATA_DIR)) { $env:APP_DATA_DIR = (Join-Path (Get-Location) "data") }
# AUTH_DB_PATH: SQLite database for user authentication (username/password)
if ([string]::IsNullOrWhiteSpace($env:AUTH_DB_PATH)) { $env:AUTH_DB_PATH = (Join-Path (Get-Location) "auth.db") }
# SESSION_DB_PATH: SQLite database for Express session storage
if ([string]::IsNullOrWhiteSpace($env:SESSION_DB_PATH)) { $env:SESSION_DB_PATH = (Join-Path (Get-Location) "sessions.db") }

# ---------- WAP Push / NowSMS Gateway ----------
# WAP Push sends real-time notifications to the phone when new WhatsApp messages arrive.
# Requires a NowSMS gateway (or compatible WAP Push SI provider).
#
# NOTE: WAP_PUSH_ENABLED and WAP_PUSH_PHONE set the initial defaults only.
# At runtime, all WAP Push options (enable/disable, expiration, auto-delete,
# history limit) are configurable from the Settings > WAP Push page.
#
# WAP_PUSH_ENABLED: initial default for WAP Push master switch (true/false/1/0/yes/no)
if ([string]::IsNullOrWhiteSpace($env:WAP_PUSH_ENABLED)) { $env:WAP_PUSH_ENABLED = "true" }
# WAP_PUSH_BASE_URL: NowSMS HTTP endpoint for sending WAP Push SI messages
if ([string]::IsNullOrWhiteSpace($env:WAP_PUSH_BASE_URL)) { $env:WAP_PUSH_BASE_URL = "" }
# WAP_PUSH_AUTH: HTTP Authorization header for NowSMS (Basic base64(user:pass))
if ([string]::IsNullOrWhiteSpace($env:WAP_PUSH_AUTH)) { $env:WAP_PUSH_AUTH = "" }
# WAP_PUSH_PHONE: initial phone number for WAP Push notifications (empty = disabled)
# Can be changed at runtime from Settings > WAP Push
if ([string]::IsNullOrWhiteSpace($env:WAP_PUSH_PHONE)) { $env:WAP_PUSH_PHONE = "" }
# WAP_SERVER_BASE: public URL of this server reachable from the phone's mobile network.
# Used in WAP Push SI links so the phone can open the chat directly.
# IMPORTANT: must NOT be 127.0.0.1 — the phone needs to reach this from the carrier network.
if ([string]::IsNullOrWhiteSpace($env:WAP_SERVER_BASE)) { $env:WAP_SERVER_BASE = "" }

# ---------- HTTPS / TLS ----------
# Set HTTPS_ENABLED to true/1/yes/on to enable HTTPS with auto Let's Encrypt certificates.
# Requires a valid domain name pointing to this server and port 443 accessible.
if ([string]::IsNullOrWhiteSpace($env:HTTPS_ENABLED)) { $env:HTTPS_ENABLED = "false" }
# HTTPS_DOMAIN: domain name for the Let's Encrypt certificate
if ([string]::IsNullOrWhiteSpace($env:HTTPS_DOMAIN)) { $env:HTTPS_DOMAIN = "example.com" }
# HTTPS_EMAIL: email for Let's Encrypt registration and expiry notifications
if ([string]::IsNullOrWhiteSpace($env:HTTPS_EMAIL)) { $env:HTTPS_EMAIL = "admin@example.com" }
# HTTPS_PORT: HTTPS listening port (443 for standard HTTPS)
if ([string]::IsNullOrWhiteSpace($env:HTTPS_PORT)) { $env:HTTPS_PORT = "443" }
# HTTPS_CERTS_DIR: directory to store Let's Encrypt certificates
if ([string]::IsNullOrWhiteSpace($env:HTTPS_CERTS_DIR)) { $env:HTTPS_CERTS_DIR = (Join-Path (Get-Location) "certs") }

# ---------- Authentication ----------
# AUTH_ENABLED: set to false/0/no/off to disable login (anyone can access the client)
# Default: true (login required). Set to "false" for single-user/local deployments.
if ([string]::IsNullOrWhiteSpace($env:AUTH_ENABLED)) { $env:AUTH_ENABLED = "false" }

# ---------- Markup Mode ----------
# MARKUP_MODE: controls the output format for all WML pages.
#   "wml"   = WML 1.0 for WAP phones (default)
#   "xhtml" = XHTML Mobile Profile 1.0 (WAP-277) with WCSS for WAP 2.0 browsers
#   "html5" = HTML5 with WhatsApp-themed CSS (for modern browsers)
if ([string]::IsNullOrWhiteSpace($env:MARKUP_MODE)) { $env:MARKUP_MODE = "xhtml" }
# UPLOAD_MARKUP_MODE: controls the output format for the upload page (/opera/send).
#   "xhtml" = XHTML-MP minimal upload form (no JS, no chunked upload)
#   "html5" = full HTML5 upload page with chunked upload, progress bar, CSS (default)
if ([string]::IsNullOrWhiteSpace($env:UPLOAD_MARKUP_MODE)) { $env:UPLOAD_MARKUP_MODE = "xhtml" }

# ---------- WhatsApp Pairing ----------
# WA_PHONE_NUMBER: if set, uses pairing code instead of QR code.
# Format: digits only with country code (e.g. 393401234567 for Italy +39).
# If empty or unset, the server shows a QR code for scanning.
# Example: $env:WA_PHONE_NUMBER = "393401234567"

# ---------- Print configuration ----------
Write-Host "[env] NODE_ENV=$env:NODE_ENV"
Write-Host "[env] PORT=$env:PORT"
Write-Host "[env] RTSP_PORT=$env:RTSP_PORT"
Write-Host "[env] WML_REFRESH_TIMER_UNITS=$env:WML_REFRESH_TIMER_UNITS"
Write-Host "[env] APP_DATA_DIR=$env:APP_DATA_DIR"
Write-Host "[env] AUTH_DB_PATH=$env:AUTH_DB_PATH"
Write-Host "[env] SESSION_DB_PATH=$env:SESSION_DB_PATH"
Write-Host "[env] HTTPS_ENABLED=$env:HTTPS_ENABLED"
Write-Host "[env] HTTPS_DOMAIN=$env:HTTPS_DOMAIN"
Write-Host "[env] HTTPS_EMAIL=$env:HTTPS_EMAIL"
Write-Host "[env] HTTPS_PORT=$env:HTTPS_PORT"
Write-Host "[env] HTTPS_CERTS_DIR=$env:HTTPS_CERTS_DIR"
Write-Host "[env] WAP_SERVER_BASE=$env:WAP_SERVER_BASE"
Write-Host "[env] WAP_PUSH_BASE_URL=$env:WAP_PUSH_BASE_URL"
Write-Host "[env] WAP_PUSH_AUTH=$env:WAP_PUSH_AUTH"
Write-Host "[env] WAP_PUSH_ENABLED=$env:WAP_PUSH_ENABLED"
Write-Host "[env] WAP_PUSH_PHONE=$env:WAP_PUSH_PHONE"
Write-Host "[env] AUTH_ENABLED=$env:AUTH_ENABLED"
Write-Host "[env] MARKUP_MODE=$env:MARKUP_MODE"
Write-Host "[env] UPLOAD_MARKUP_MODE=$env:UPLOAD_MARKUP_MODE"
Write-Host "[env] WA_PHONE_NUMBER=$env:WA_PHONE_NUMBER"

npm start
