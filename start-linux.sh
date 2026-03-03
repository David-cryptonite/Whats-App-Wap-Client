#!/usr/bin/env bash
# ============================================================
# WhatsApp WAP Client - Linux/macOS Startup Script
# ============================================================
# Sets all environment variables with sensible defaults and
# starts the Node.js server via npm start.
#
# Usage:
#   ./start-linux.sh                                    # uses all defaults
#   PORT=8080 ./start-linux.sh                          # override port
#   WA_PHONE_NUMBER=393401234567 ./start-linux.sh       # pairing code
#   WAP_PUSH_ENABLED=false ./start-linux.sh             # disable push
#
# All variables use "${VAR:-default}" syntax, so you can
# override any value by setting it before running this script.
# ============================================================

set -euo pipefail

# ---------- Server ----------
# NODE_ENV: "development" or "production" (affects logging verbosity)
export NODE_ENV="${NODE_ENV:-development}"
# PORT: HTTP port the WML server listens on
export PORT="${PORT:-3500}"
# RTSP_PORT: RTSP streaming port for video playback on WAP devices
export RTSP_PORT="${RTSP_PORT:-8554}"
# WML_REFRESH_TIMER_UNITS: WML timer units (1 unit = 0.1s). 100 = 10 seconds
export WML_REFRESH_TIMER_UNITS="${WML_REFRESH_TIMER_UNITS:-100}"
# APP_DATA_DIR: directory for persistent JSON data (contacts, chats, messages, settings)
export APP_DATA_DIR="${APP_DATA_DIR:-$(pwd)/data}"
# AUTH_DB_PATH: SQLite database for user authentication (username/password)
export AUTH_DB_PATH="${AUTH_DB_PATH:-$(pwd)/auth.db}"
# SESSION_DB_PATH: SQLite database for Express session storage
export SESSION_DB_PATH="${SESSION_DB_PATH:-$(pwd)/sessions.db}"

# ---------- WAP Push / NowSMS Gateway ----------
# WAP Push sends real-time notifications to the phone when new WhatsApp messages arrive.
# Requires a NowSMS gateway (or compatible WAP Push SI provider).
#
# NOTE: WAP_PUSH_ENABLED and WAP_PUSH_PHONE set the initial defaults only.
# At runtime, all WAP Push options (enable/disable, expiration, auto-delete,
# history limit) are configurable from the Settings > WAP Push page.
#
# WAP_PUSH_ENABLED: initial default for WAP Push master switch (true/false/1/0/yes/no)
export WAP_PUSH_ENABLED="${WAP_PUSH_ENABLED:-true}"
# WAP_PUSH_BASE_URL: NowSMS HTTP endpoint for sending WAP Push SI messages
export WAP_PUSH_BASE_URL="${WAP_PUSH_BASE_URL:-}"
# WAP_PUSH_AUTH: HTTP Authorization header for NowSMS (Basic base64(user:pass))
export WAP_PUSH_AUTH="${WAP_PUSH_AUTH:-}"
# WAP_PUSH_PHONE: initial phone number for WAP Push notifications (empty = disabled)
# Can be changed at runtime from Settings > WAP Push
export WAP_PUSH_PHONE="${WAP_PUSH_PHONE:-}"
# WAP_SERVER_BASE: public URL of this server reachable from the phone's mobile network.
# Used in WAP Push SI links so the phone can open the chat directly.
# IMPORTANT: must NOT be 127.0.0.1 — the phone needs to reach this from the carrier network.
export WAP_SERVER_BASE="${WAP_SERVER_BASE:-}"

# ---------- HTTPS / TLS ----------
# Set HTTPS_ENABLED to true/1/yes/on to enable HTTPS with auto Let's Encrypt certificates.
# Requires a valid domain name pointing to this server and port 443 accessible.
export HTTPS_ENABLED="${HTTPS_ENABLED:-false}"
# HTTPS_DOMAIN: domain name for the Let's Encrypt certificate
export HTTPS_DOMAIN="${HTTPS_DOMAIN:-example.com}"
# HTTPS_EMAIL: email for Let's Encrypt registration and expiry notifications
export HTTPS_EMAIL="${HTTPS_EMAIL:-admin@example.com}"
# HTTPS_PORT: HTTPS listening port (443 for standard HTTPS)
export HTTPS_PORT="${HTTPS_PORT:-443}"
# HTTPS_CERTS_DIR: directory to store Let's Encrypt certificates
export HTTPS_CERTS_DIR="${HTTPS_CERTS_DIR:-$(pwd)/certs}"

# ---------- Authentication ----------
# AUTH_ENABLED: set to false/0/no/off to disable login (anyone can access the client)
# Default: true (login required). Set to "false" for single-user/local deployments.
export AUTH_ENABLED="${AUTH_ENABLED:-false}"

# ---------- Markup Mode ----------
# MARKUP_MODE: controls the output format for all WML pages.
#   "wml"   = WML 1.0 for WAP phones (default)
#   "xhtml" = XHTML Mobile Profile 1.0 (WAP-277) with WCSS for WAP 2.0 browsers
#   "html5" = HTML5 with WhatsApp-themed CSS (for modern browsers)
export MARKUP_MODE="${MARKUP_MODE:-xhtml}"
# UPLOAD_MARKUP_MODE: controls the output format for the upload page (/opera/send).
#   "xhtml" = XHTML-MP minimal upload form (no JS, no chunked upload)
#   "html5" = full HTML5 upload page with chunked upload, progress bar, CSS (default)
export UPLOAD_MARKUP_MODE="${UPLOAD_MARKUP_MODE:-xhtml}"

# ---------- WhatsApp Pairing ----------
# WA_PHONE_NUMBER: if set, uses pairing code instead of QR code.
# Format: digits only with country code (e.g. 393401234567 for Italy +39).
# If empty or unset, the server shows a QR code for scanning.
# Example: export WA_PHONE_NUMBER="393401234567"
export WA_PHONE_NUMBER="${WA_PHONE_NUMBER:-}"

# ---------- Print configuration ----------
echo "[env] NODE_ENV=$NODE_ENV"
echo "[env] PORT=$PORT"
echo "[env] RTSP_PORT=$RTSP_PORT"
echo "[env] WML_REFRESH_TIMER_UNITS=$WML_REFRESH_TIMER_UNITS"
echo "[env] APP_DATA_DIR=$APP_DATA_DIR"
echo "[env] AUTH_DB_PATH=$AUTH_DB_PATH"
echo "[env] SESSION_DB_PATH=$SESSION_DB_PATH"
echo "[env] HTTPS_ENABLED=$HTTPS_ENABLED"
echo "[env] HTTPS_DOMAIN=$HTTPS_DOMAIN"
echo "[env] HTTPS_EMAIL=$HTTPS_EMAIL"
echo "[env] HTTPS_PORT=$HTTPS_PORT"
echo "[env] HTTPS_CERTS_DIR=$HTTPS_CERTS_DIR"
echo "[env] WAP_SERVER_BASE=$WAP_SERVER_BASE"
echo "[env] WAP_PUSH_BASE_URL=$WAP_PUSH_BASE_URL"
echo "[env] WAP_PUSH_AUTH=$WAP_PUSH_AUTH"
echo "[env] WAP_PUSH_ENABLED=$WAP_PUSH_ENABLED"
echo "[env] WAP_PUSH_PHONE=$WAP_PUSH_PHONE"
echo "[env] AUTH_ENABLED=$AUTH_ENABLED"
echo "[env] MARKUP_MODE=$MARKUP_MODE"
echo "[env] UPLOAD_MARKUP_MODE=$UPLOAD_MARKUP_MODE"
echo "[env] WA_PHONE_NUMBER=$WA_PHONE_NUMBER"

npm start
