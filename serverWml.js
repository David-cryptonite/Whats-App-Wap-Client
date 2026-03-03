// Multi-threading and clustering for high performance
import cluster from 'cluster';
import os from 'os';

import express from 'express';
import compression from 'compression';
import http from 'http';
import https from 'https';
import acme from 'acme-client';
import {
  makeWASocket,
  useMultiFileAuthState,
  DisconnectReason,
  fetchLatestBaileysVersion,
  downloadMediaMessage,
  getContentType,
  extractMessageContent,
  delay,
  jidNormalizedUser,
  areJidsSameUser,
  jidDecode,
  Browsers
} from '@whiskeysockets/baileys';
import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import { dirname } from 'path';
import axios from 'axios';
import qrcode from 'qrcode-terminal';
import QRCode from 'qrcode';
import helmet from 'helmet';
import rateLimit from 'express-rate-limit';
import winston from 'winston';
import { initializeDependencies, enhancedInitialSync } from './loadChatUtils.js';
import PersistentStorage from './persistentStorage.js';
import sharp from 'sharp';
import ffmpeg from 'ffmpeg-static';
import { exec, spawn } from 'child_process';
import iconv from 'iconv-lite';
import net from 'net';
import dgram from 'dgram';
import Busboy from 'busboy';

import crypto from 'crypto';
import bcrypt from 'bcrypt';
import Database from 'better-sqlite3';
import session from 'express-session';
import SqliteStore from 'better-sqlite3-session-store';
const BetterSqlite3Store = SqliteStore(session);

const PROJECT_DIR = path.dirname(fileURLToPath(import.meta.url));
const APP_DATA_DIR = process.env.APP_DATA_DIR || path.join(PROJECT_DIR, 'data');
if (!fs.existsSync(APP_DATA_DIR)) {
  fs.mkdirSync(APP_DATA_DIR, { recursive: true });
}

function isWritableDbTarget(dbPath) {
  try {
    if (fs.existsSync(dbPath)) {
      fs.accessSync(dbPath, fs.constants.W_OK);
    } else {
      fs.accessSync(path.dirname(dbPath), fs.constants.W_OK);
    }
    return true;
  } catch {
    return false;
  }
}

function resolveDbPath(primaryPath, fallbackFilename, label) {
  if (isWritableDbTarget(primaryPath)) {
    return primaryPath;
  }
  const fallbackPath = path.join(APP_DATA_DIR, fallbackFilename);
  console.warn(`[DB] ${label} primary path not writable: ${primaryPath}`);
  console.warn(`[DB] ${label} using fallback path: ${fallbackPath}`);
  return fallbackPath;
}

// ============ AUTH DATABASE SETUP ============
const authDbPath = resolveDbPath(
  process.env.AUTH_DB_PATH || path.join(PROJECT_DIR, 'auth.db'),
  'auth.db',
  'auth'
);
const authDb = new Database(authDbPath);
authDb.pragma('journal_mode = WAL');
authDb.exec(`CREATE TABLE IF NOT EXISTS config (key TEXT PRIMARY KEY, value TEXT)`);
const existingPw = authDb.prepare('SELECT value FROM config WHERE key = ?').get('password_hash');
if (!existingPw) {
  const defaultHash = bcrypt.hashSync('admin', 10);
  authDb.prepare('INSERT INTO config (key, value) VALUES (?, ?)').run('password_hash', defaultHash);
  console.log('[AUTH] Default password set to "" — change it from settings!');
}
const existingUser = authDb.prepare('SELECT value FROM config WHERE key = ?').get('username');
if (!existingUser) {
  authDb.prepare('INSERT INTO config (key, value) VALUES (?, ?)').run('username', 'admin');
  console.log('[AUTH] Default username set to "admin" — change it from settings!');
}
// Persist session secret so sessions survive server restarts
let sessionSecret;
const existingSecret = authDb.prepare('SELECT value FROM config WHERE key = ?').get('session_secret');
if (existingSecret) {
  sessionSecret = existingSecret.value;
} else {
  sessionSecret = crypto.randomBytes(32).toString('hex');
  authDb.prepare('INSERT INTO config (key, value) VALUES (?, ?)').run('session_secret', sessionSecret);
}

// ============ RTSP SERVER FOR SYMBIAN/REALPLAYER ============
const RTSP_PORT = Number.parseInt(process.env.RTSP_PORT || '8554', 10) || 8554;
function normalizeWmlRefreshUnits(value) {
  const raw = Number.parseInt(String(value ?? ""), 10);
  if (!Number.isFinite(raw)) return 100;
  return Math.min(9999, Math.max(1, raw));
}
const rtspSessions = new Map(); // Track active RTSP sessions

class RTSPServer {
  constructor(port = RTSP_PORT) {
    this.port = port;
    this.server = null;
    this.sessions = new Map();
    this.ffmpegProcesses = new Map();
  }

  start() {
    this.server = net.createServer((socket) => {
      console.log(`[RTSP] Client connected: ${socket.remoteAddress}:${socket.remotePort}`);

      let buffer = '';

      socket.on('data', (data) => {
        buffer += data.toString();

        // RTSP requests end with \r\n\r\n
        while (buffer.includes('\r\n\r\n')) {
          const endIndex = buffer.indexOf('\r\n\r\n') + 4;
          const request = buffer.substring(0, endIndex);
          buffer = buffer.substring(endIndex);

          this.handleRequest(socket, request);
        }
      });

      socket.on('close', () => {
        console.log(`[RTSP] Client disconnected`);
        this.cleanupSession(socket);
      });

      socket.on('error', (err) => {
        console.error(`[RTSP] Socket error:`, err.message);
      });
    });

    this.server.listen(this.port, '0.0.0.0', () => {
      console.log(`[RTSP] Server listening on rtsp://0.0.0.0:${this.port}`);
    });
  }

  handleRequest(socket, request) {
    const lines = request.split('\r\n');
    const [method, uri] = lines[0].split(' ');

    // Parse headers
    const headers = {};
    for (let i = 1; i < lines.length; i++) {
      const colonIndex = lines[i].indexOf(':');
      if (colonIndex > 0) {
        const key = lines[i].substring(0, colonIndex).trim();
        const value = lines[i].substring(colonIndex + 1).trim();
        headers[key] = value;
      }
    }

    const cseq = headers['CSeq'] || '1';
    console.log(`[RTSP] ${method} ${uri} CSeq:${cseq}`);

    switch (method) {
      case 'OPTIONS':
        this.handleOptions(socket, cseq);
        break;
      case 'DESCRIBE':
        this.handleDescribe(socket, uri, cseq);
        break;
      case 'SETUP':
        this.handleSetup(socket, uri, cseq, headers);
        break;
      case 'PLAY':
        this.handlePlay(socket, uri, cseq, headers);
        break;
      case 'TEARDOWN':
        this.handleTeardown(socket, cseq);
        break;
      default:
        this.sendResponse(socket, 501, cseq, 'Not Implemented');
    }
  }

  handleOptions(socket, cseq) {
    console.log(`[RTSP] OPTIONS request, CSeq=${cseq}`);
    const response = `RTSP/1.0 200 OK\r\n` +
      `CSeq: ${cseq}\r\n` +
      `Server: WhatsApp-WAP-RTSP/1.0\r\n` +
      `Public: OPTIONS, DESCRIBE, SETUP, PLAY, PAUSE, TEARDOWN\r\n` +
      `\r\n`;
    socket.write(response);
    console.log(`[RTSP] OPTIONS response sent`);
  }

  handleDescribe(socket, uri, cseq) {
    console.log(`[RTSP] DESCRIBE received for URI: ${uri}`);

    // Extract messageId from URI: rtsp://server:8554/video/messageId.3gp
    const match = uri.match(/\/(video|audio)\/([^.]+)\.(\w+)/);
    if (!match) {
      console.log(`[RTSP] DESCRIBE 404 - URI did not match pattern, uri=${uri}`);
      this.sendResponse(socket, 404, cseq, 'Not Found');
      return;
    }

    const [, type, messageId, format] = match;
    console.log(`[RTSP] DESCRIBE parsed: type=${type}, messageId=${messageId}, format=${format}`);

    const sessionId = crypto.randomBytes(8).toString('hex');

    // Store session info
    this.sessions.set(sessionId, {
      socket,
      type,
      messageId: decodeURIComponent(messageId),
      format,
      clientPort: null,
      serverPort: null
    });

    // Get client IP for Content-Base
    const clientIp = socket.localAddress ? socket.localAddress.replace('::ffff:', '') : '0.0.0.0';
    const contentBase = `rtsp://${clientIp}:${this.port}/${type}/${messageId}.${format}/`;

    // SDP for the media
    const sdp = type === 'video'
      ? this.getVideoSDP(messageId, format, clientIp)
      : this.getAudioSDP(messageId, format, clientIp);

    // Use Buffer.byteLength for correct Content-Length (bytes, not chars)
    const sdpBytes = Buffer.byteLength(sdp, 'utf8');
    console.log(`[RTSP] DESCRIBE SDP length: ${sdpBytes} bytes`);
    console.log(`[RTSP] DESCRIBE Content-Base: ${contentBase}`);
    console.log(`[RTSP] DESCRIBE SDP:\n${sdp}`);

    const response = `RTSP/1.0 200 OK\r\n` +
      `CSeq: ${cseq}\r\n` +
      `Server: WhatsApp-WAP-RTSP/1.0\r\n` +
      `Content-Base: ${contentBase}\r\n` +
      `Content-Type: application/sdp\r\n` +
      `Content-Length: ${sdpBytes}\r\n` +
      `Cache-Control: no-cache\r\n` +
      `\r\n` +
      sdp;

    console.log(`[RTSP] DESCRIBE response sent, sessionId=${sessionId}`);
    socket.write(response);
    socket.sessionId = sessionId;
  }

  getVideoSDP(messageId, format, serverIp = '0.0.0.0') {
    // SDP compatible with Nokia/Symbian RealPlayer
    // b=AS: bandwidth in kbps - ESTREMAMENTE BASSO per GPRS
    const sessionId = Date.now();
    return `v=0\r\n` +
      `o=- ${sessionId} ${sessionId} IN IP4 ${serverIp}\r\n` +
      `s=WhatsApp Video\r\n` +
      `i=Video stream from WhatsApp\r\n` +
      `c=IN IP4 0.0.0.0\r\n` +
      `t=0 0\r\n` +
      `b=AS:24\r\n` +         // MODIFICATO: Da 80 a 24 (adatto a GPRS reale)
      `a=recvonly\r\n` +
      `m=video 0 RTP/AVP 34\r\n` +
      `b=AS:20\r\n` +         // MODIFICATO: Assegnazione bandwidth specifica video
      `a=rtpmap:34 H263/90000\r\n` +
      `a=fmtp:34 QCIF=1\r\n` +
      `a=control:trackID=0\r\n` +
      `m=audio 0 RTP/AVP 96\r\n` +
      `b=AS:10\r\n` +         // MODIFICATO: Assegnazione bandwidth specifica audio
      `a=rtpmap:96 AMR/8000/1\r\n` +
      `a=fmtp:96 octet-align=1\r\n` +
      `a=control:trackID=1\r\n`;
  }

  getAudioSDP(messageId, format, serverIp = '0.0.0.0') {
    // SDP compatible with Nokia/Symbian RealPlayer
    // b=AS: bandwidth in kbps - low values for GPRS/EDGE compatibility
    const sessionId = Date.now();
    return `v=0\r\n` +
      `o=- ${sessionId} ${sessionId} IN IP4 ${serverIp}\r\n` +
      `s=WhatsApp Audio\r\n` +
      `i=Audio stream from WhatsApp\r\n` +
      `c=IN IP4 0.0.0.0\r\n` +
      `t=0 0\r\n` +
      `b=AS:16\r\n` +
      `a=recvonly\r\n` +
      `m=audio 0 RTP/AVP 96\r\n` +
      `b=AS:13\r\n` +
      `a=rtpmap:96 AMR/8000/1\r\n` +
      `a=fmtp:96 octet-align=1\r\n` +
      `a=control:trackID=0\r\n`;
  }

  handleSetup(socket, uri, cseq, headers) {
    console.log(`[RTSP] SETUP received for URI: ${uri}`);
    console.log(`[RTSP] SETUP headers:`, JSON.stringify(headers));

    // Try to get sessionId from socket or headers
    let sessionId = socket.sessionId || headers['Session'];
    let session = sessionId ? this.sessions.get(sessionId) : null;

    // If no session found, try to find by socket
    if (!session) {
      for (const [sid, sess] of this.sessions.entries()) {
        if (sess.socket === socket) {
          sessionId = sid;
          session = sess;
          break;
        }
      }
    }

    if (!session) {
      console.log(`[RTSP] SETUP 454 - Session not found, sessionId=${sessionId}`);
      this.sendResponse(socket, 454, cseq, 'Session Not Found');
      return;
    }

    // Parse client transport header
    const transport = headers['Transport'] || '';
    const clientPortMatch = transport.match(/client_port=(\d+)-(\d+)/);
    const clientRtpPort = clientPortMatch ? parseInt(clientPortMatch[1]) : 5000;

    console.log(`[RTSP] SETUP transport: ${transport}, clientRtpPort=${clientRtpPort}`);

    // Determine which track is being set up (video=0, audio=1)
    const trackMatch = uri.match(/trackID=(\d+)/);
    const trackId = trackMatch ? parseInt(trackMatch[1]) : 0;

    console.log(`[RTSP] SETUP trackId=${trackId}`);

    // Fixed server ports for easier firewall config
    // Video: 6970, Audio: 6980
    const serverRtpPort = trackId === 0 ? 6970 : 6980;

    session.clientAddress = (socket.remoteAddress || '').replace('::ffff:', '');

    if (trackId === 0) {
      // Video track (or first audio track for audio-only)
      session.videoClientPort = clientRtpPort;
      session.videoServerPort = serverRtpPort;
    } else {
      // Audio track
      session.audioClientPort = clientRtpPort;
      session.audioServerPort = serverRtpPort;
    }

    const response = `RTSP/1.0 200 OK\r\n` +
      `CSeq: ${cseq}\r\n` +
      `Server: WhatsApp-WAP-RTSP/1.0\r\n` +
      `Session: ${sessionId};timeout=60\r\n` +
      `Transport: RTP/AVP;unicast;client_port=${clientRtpPort}-${clientRtpPort + 1};server_port=${serverRtpPort}-${serverRtpPort + 1}\r\n` +
      `\r\n`;

    console.log(`[RTSP] SETUP response sent for track ${trackId}`);
    socket.write(response);
  }

  async handlePlay(socket, uri, cseq, headers) {
    const sessionId = socket.sessionId || headers['Session'];
    const session = this.sessions.get(sessionId);

    if (!session) {
      this.sendResponse(socket, 454, cseq, 'Session Not Found');
      return;
    }

    const response = `RTSP/1.0 200 OK\r\n` +
      `CSeq: ${cseq}\r\n` +
      `Session: ${sessionId}\r\n` +
      `Range: npt=0.000-\r\n` +
      `\r\n`;

    socket.write(response);

    // Start streaming with ffmpeg — fire-and-forget but capture errors
    this.startStreaming(session, sessionId).catch(err =>
      console.error(`[RTSP] Streaming failed for session ${sessionId}:`, err)
    );
  }
  async startStreaming(session, sessionId) {
    const { type, messageId, format, clientAddress, videoClientPort, videoServerPort, audioClientPort, audioServerPort } = session;

    console.log(`[RTSP] Starting ${type} stream for ${messageId} to ${clientAddress}`);
    console.log(`[RTSP] Video: client=${videoClientPort}, server=${videoServerPort}`);
    console.log(`[RTSP] Audio: client=${audioClientPort}, server=${audioServerPort}`);

    // --- TROVA MEDIA --- O(1) lookup via messageStore
    let mediaPath = null;

    const found = messageStore.get(messageId);
    if (found) {
      try {
        const mediaData = await downloadMediaMessage(
          found,
          "buffer",
          {},
          { logger, reuploadRequest: sock?.updateMediaMessage }
        );

        mediaPath = safeTempPath(`rtsp_${messageId}_input.${type === 'video' ? 'mp4' : 'ogg'}`);
        await fs.promises.writeFile(mediaPath, mediaData);
        console.log(`[RTSP] Media saved to ${mediaPath}`);
      } catch (err) {
        console.error(`[RTSP] Failed to download media:`, err);
        return;
      }
    }

    if (!mediaPath) {
      console.error(`[RTSP] Message not found: ${messageId}`);
      return;
    }

    let ffmpegArgs;

    // --- GESTIONE VIDEO (CON pkt_size=1400) ---
    if (type === 'video') {
      if (audioClientPort) {
        ffmpegArgs = [
          '-re',
          '-i', mediaPath,
          
          // --- VIDEO (Output 1) ---
          '-map', '0:v:0',
          '-c:v', 'h263',
          '-s', '176x144',      // QCIF Standard
          '-r', '5',            // 5 fps stabile
          '-b:v', '15k',        // Bitrate basso
          '-maxrate', '18k',
          '-profile:v', '0',     // H.263 Baseline Profile
          '-g', '10',             // Keyframe interval
          '-pix_fmt', 'yuv420p', // Fondamentale per H.263
          
          '-f', 'rtp',
          '-payload_type', '34',
          `rtp://${clientAddress}:${videoClientPort || 5000}?pkt_size=1400&localport=${videoServerPort}`, // MANTENIAMO pkt_size QUI
          
          // --- AUDIO (Output 2) ---
          '-map', '0:a:0',
          '-c:a', 'libopencore_amrnb',
          '-ar', '8000',
          '-ac', '1',
          '-b:a', '5.9k',         // Bitrate standard AMR
          
          '-f', 'rtp',
          '-payload_type', '96',
          `rtp://${clientAddress}:${audioClientPort || 5002}?localport=${audioServerPort}` // RIMOSSO pkt_size DA QUI
        ];
      } else {
        // Fallback senza audio
        ffmpegArgs = [
          '-re',
          '-i', mediaPath,
          '-c:v', 'h263',
          '-s', '176x144',
          '-r', '5',
          '-b:v', '15k',
          '-maxrate', '18k',
          '-profile:v', '0',
          '-g', '30',
          '-pix_fmt', 'yuv420p',
          '-f', 'rtp_mpegts',
          `rtp://${clientAddress}:${videoClientPort || 5000}?pkt_size=1400&localport=${videoServerPort}`
        ];
      }
    } 
    // --- GESTIONE AUDIO (SOLO) ---
    else if (type === 'audio') {
      ffmpegArgs = [
        '-re',
        '-i', mediaPath,
        '-c:a', 'libopencore_amrnb',
        '-ar', '8000',
        '-ac', '1',
        '-b:a', '5.9k',
        '-f', 'rtp',
        '-payload_type', '96',
        `rtp://${clientAddress}:${audioClientPort || 5000}?localport=${audioServerPort || 6970}` // NESSUN pkt_size QUI
      ];
    }

    console.log(`[RTSP] FFmpeg args: ${ffmpegArgs.join(' ')}`);

    const ffmpegProcess = spawn(ffmpeg, ffmpegArgs);
    this.ffmpegProcesses.set(sessionId, ffmpegProcess);

    ffmpegProcess.stderr.on('data', (data) => {
      console.log(`[RTSP/FFmpeg] ${data.toString().trim()}`);
    });

    ffmpegProcess.on('error', (err) => {
      console.error(`[RTSP] FFmpeg spawn error:`, err);
      this.ffmpegProcesses.delete(sessionId);
      if (mediaPath) {
        fs.promises.unlink(mediaPath).catch(() => {});
      }
    });

    ffmpegProcess.on('close', (code) => {
      console.log(`[RTSP] FFmpeg process ended with code ${code}`);
      if (code !== 0) {
        console.error(`[RTSP] FFmpeg exited with error code ${code} for session ${sessionId}`);
      }
      this.ffmpegProcesses.delete(sessionId);

      // Cleanup temp file
      if (mediaPath) {
        fs.promises.unlink(mediaPath).catch(() => {});
      }
    });

    // Timeout: kill FFmpeg if stuck for more than 5 minutes
    const rtspTimeout = setTimeout(() => {
      if (this.ffmpegProcesses.has(sessionId)) {
        console.log(`[RTSP] FFmpeg timeout (5min) for session ${sessionId}, killing...`);
        ffmpegProcess.kill('SIGKILL');
      }
    }, 300000);
    ffmpegProcess.on('close', () => clearTimeout(rtspTimeout));
  }

  handleTeardown(socket, cseq) {
    const sessionId = socket.sessionId;

    this.cleanupSession(socket);

    const response = `RTSP/1.0 200 OK\r\n` +
      `CSeq: ${cseq}\r\n` +
      `\r\n`;

    socket.write(response);
  }

  cleanupSession(socket) {
    const sessionId = socket.sessionId;
    if (sessionId) {
      this.sessions.delete(sessionId);

      const ffmpegProcess = this.ffmpegProcesses.get(sessionId);
      if (ffmpegProcess) {
        ffmpegProcess.kill('SIGTERM');
        this.ffmpegProcesses.delete(sessionId);
      }
    }
  }

  sendResponse(socket, code, cseq, message) {
    const response = `RTSP/1.0 ${code} ${message}\r\n` +
      `CSeq: ${cseq}\r\n` +
      `\r\n`;
    socket.write(response);
  }
}

// Global RTSP server instance
let rtspServer = null;

// Map per tracciare i timeout pendenti (opzionale, per cancellare se necessario)
const pendingDeletes = new Map();

/**
 * Genera un WAPSIID univoco
 */
function generateWAPSIID() {
  return crypto.randomBytes(3).toString('hex'); // "a3f2"
}

// ESM __dirname replacement
const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

// ============ PRODUCTION-GRADE HTTP CLIENT CONFIGURATION ============
// Configure axios for optimal performance with connection pooling
const axiosAgent = new http.Agent({
  keepAlive: true,
  keepAliveMsecs: 30000,
  maxSockets: 50,
  maxFreeSockets: 10,
  timeout: 60000,
  scheduling: 'lifo' // Last In First Out for better performance
});

axios.defaults.httpAgent = axiosAgent;
axios.defaults.timeout = 30000;
axios.defaults.maxRedirects = 5;

// Configurazione Whisper e TTS
let transcriber = null;
let transcriptionEnabled = false;
let ttsModel = null;
let ttsSpeakerEmbeddings = null;
let ttsEnabled = false;

// Inizializza il modello Whisper con import dinamico
// Using whisper-base for better accuracy with Italian and English
async function initWhisperModel() {
  try {
    console.log("Initializing Whisper model (base - better accuracy)...");

    // Usa import dinamico per caricare il modulo ESM
    const { pipeline } = await import("@xenova/transformers");

    // Using whisper-base for better transcription quality
    // whisper-tiny: 39MB, lower accuracy
    // whisper-base: 74MB, much better accuracy for Italian & English
    transcriber = await pipeline(
      "automatic-speech-recognition",
      "Xenova/whisper-base",
      {
        // ⚡ 74MB - better accuracy than tiny (39MB)
        quantized: true, // 🔥 Usa 8-bit per ridurre RAM
        local_files_only: false,
      }
    );

    transcriptionEnabled = true;
    console.log("✓ Whisper model loaded successfully (base model - high accuracy)");
    console.log("✓ Supported languages: Italian (it) + English (en) with auto-detection");
  } catch (error) {
    console.error("Whisper model initialization failed:", error);
    transcriptionEnabled = false;
  }
}

// Check if espeak is available (local TTS for Raspberry Pi)
async function initTTSModel() {
  try {
    console.log("Checking for local TTS engine (espeak)...");

    // Check if espeak is installed
    await new Promise((resolve, reject) => {
      exec('which espeak || which espeak-ng', (error, stdout) => {
        if (error || !stdout.trim()) {
          reject(new Error('espeak not found. Install with: sudo apt-get install espeak'));
        } else {
          resolve(stdout.trim());
        }
      });
    });

    ttsEnabled = true;
    console.log("✓ Local TTS ready (espeak) - English & Italian, fully offline");
  } catch (error) {
    console.error("⚠ Local TTS not available:", error.message);
    console.error("Install espeak: sudo apt-get install espeak");
    ttsEnabled = false;
  }
}

// Funzione di trascrizione con Whisper - IMPROVED VERSION
// Supports Italian, English, and auto-detection for better accuracy
async function transcribeAudioWithWhisper(audioBuffer, language = 'auto') {
  if (!transcriptionEnabled || !transcriber) {
    return t('audio.unavailable');
  }

  const tempOutput = safeTempPath(`whisper_${Date.now()}_${Math.random().toString(36).slice(2,6)}.wav`);

  try {
    console.log(`Converting audio to WAV format (language: ${language})...`);

    await new Promise((resolve, reject) => {
      const proc = spawn(ffmpeg, [
        "-i", "pipe:0",
        "-ar", "16000",
        "-ac", "1",
        "-c:a", "pcm_s16le",
        "-f", "wav",
        "-",
      ]);

      const outputStream = fs.createWriteStream(tempOutput);
      outputStream.on("error", reject);

      proc.stdin.end(audioBuffer);
      proc.stdout.pipe(outputStream);

      proc.on("error", reject);
      outputStream.on("finish", resolve);
    });

    console.log("Converting WAV to Float32Array...");

    let wavBuffer;
    try {
      wavBuffer = await fs.promises.readFile(tempOutput);
    } catch (e) {
      throw new Error(`Whisper WAV conversion produced no output: ${e.message}`);
    }

    // Estrai i dati audio PCM dal file WAV
    const float32Array = wavBufferToFloat32Array(wavBuffer);

    console.log(`Transcribing with Whisper (base model, language: ${language})...`);

    // Configure transcription options based on language
    const transcriptionOptions = {
      chunk_length_s: 30,
      stride_length_s: 5,
      return_timestamps: false,
    };

    // Language selection: 'auto', 'it' (Italian), or 'en' (English)
    if (language === 'auto') {
      // Auto-detect language (Whisper will choose the best match)
      console.log("Using automatic language detection (Italian/English)");
      // Don't specify language - let Whisper detect it
    } else if (language === 'it' || language === 'en') {
      // Explicit language selection for better accuracy
      transcriptionOptions.language = language;
      console.log(`Using explicit language: ${language === 'it' ? 'Italian' : 'English'}`);
    } else {
      // Fallback to Italian for unknown languages
      console.log(`Unknown language '${language}', defaulting to Italian`);
      transcriptionOptions.language = 'it';
    }

    const result = await transcriber(float32Array, transcriptionOptions);

    const transcription = result.text || t('audio.no_transcription');

    // Clean up transcription (remove extra whitespace)
    const cleanedTranscription = transcription.trim();

    console.log(`✓ Whisper transcription successful (${cleanedTranscription.length} characters)`);
    console.log(`Transcribed text: "${cleanedTranscription.substring(0, 100)}${cleanedTranscription.length > 100 ? '...' : ''}"`);

    return cleanedTranscription;
  } catch (error) {
    console.error("Transcription failed:", error);
    return t('audio.error_transcription');
  } finally {
    unlinkSilent(tempOutput);
  }
}

// Funzione per convertire WAV buffer in Float32Array
function wavBufferToFloat32Array(wavBuffer) {
  // WAV file header is 44 bytes
  const dataOffset = 44;
  const audioData = wavBuffer.slice(dataOffset);

  // I dati sono in formato PCM 16-bit signed little-endian
  const int16Array = new Int16Array(
    audioData.buffer,
    audioData.byteOffset,
    audioData.byteLength / 2
  );

  // Converti Int16 a Float32 (range -1.0 to 1.0)
  const float32Array = new Float32Array(int16Array.length);
  for (let i = 0; i < int16Array.length; i++) {
    float32Array[i] = int16Array[i] / 32768.0; // 32768 = 2^15
  }

  return float32Array;
}
// Inizializza i modelli all'avvio
initWhisperModel();
initTTSModel();

// ============ VIDEO FRAME EXTRACTION ============
// Cache directory for video frames
const VIDEO_FRAMES_DIR = path.join(__dirname, "video_frames_cache");
if (!fs.existsSync(VIDEO_FRAMES_DIR)) {
  fs.mkdirSync(VIDEO_FRAMES_DIR, { recursive: true });
}

// ============ TEMP DIRECTORY SAFETY (Cross-Platform) ============
// Fixes ENOENT on Windows/WSL/Git Bash where /tmp may not exist.
// Fallback chain: os.tmpdir() → ./tmp (local) — works on Windows, Linux, macOS.
let TEMP_DIR = os.tmpdir();
try {
  if (!fs.existsSync(TEMP_DIR)) {
    fs.mkdirSync(TEMP_DIR, { recursive: true });
  }
  // Verify writable — some systems return a dir that exists but isn't writable
  fs.accessSync(TEMP_DIR, fs.constants.W_OK);
} catch {
  // Fallback to local ./tmp directory if system temp is broken
  TEMP_DIR = path.join(__dirname, 'tmp');
  if (!fs.existsSync(TEMP_DIR)) {
    fs.mkdirSync(TEMP_DIR, { recursive: true });
  }
  console.warn(`[TEMP] System tmpdir not writable, using fallback: ${TEMP_DIR}`);
}

// Helper: get a safe temp file path — cross-platform (Windows/Linux/macOS)
function safeTempPath(filename) {
  const fullPath = path.join(TEMP_DIR, filename);
  // If filename contains subdirectory (e.g. 'whatsapp-uploads'), ensure parent exists
  const dir = path.dirname(fullPath);
  if (dir !== TEMP_DIR && !fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true });
  }
  return fullPath;
}

// ============ MEDIA PRE-CONVERSION CACHE (for Symbian) ============
const MEDIA_CACHE_DIR = path.join(__dirname, "media_cache");
if (!fs.existsSync(MEDIA_CACHE_DIR)) {
  fs.mkdirSync(MEDIA_CACHE_DIR, { recursive: true });
}

// ============ LOCAL STICKER PACKS DIRECTORY ============
const STICKERS_DIR = path.join(__dirname, "stickers");
try {
  if (!fs.existsSync(STICKERS_DIR)) fs.mkdirSync(STICKERS_DIR, { recursive: true });
} catch (e) {
  console.error("[Stickers] Cannot create stickers dir:", e.message);
}

// ============ OPENMOJI STICKER SOURCE (ONLY) ============
// Forced to OpenMoji-only mode.
const STICKER_PROVIDER = "openmoji";
const OPENMOJI_INDEX_URLS = [
  "https://raw.githubusercontent.com/hfg-gmuend/openmoji/master/data/openmoji.json",
  "https://raw.githubusercontent.com/hfg-gmuend/openmoji/main/data/openmoji.json",
  "https://cdn.jsdelivr.net/gh/hfg-gmuend/openmoji@master/data/openmoji.json",
  "https://cdn.jsdelivr.net/gh/hfg-gmuend/openmoji@main/data/openmoji.json",
  "https://cdn.jsdelivr.net/gh/hfg-gmuend/openmoji@latest/data/openmoji.json",
];
const OPENMOJI_ASSET_BASES = [
  "https://raw.githubusercontent.com/hfg-gmuend/openmoji/master",
  "https://raw.githubusercontent.com/hfg-gmuend/openmoji/main",
  "https://cdn.jsdelivr.net/gh/hfg-gmuend/openmoji@master",
  "https://cdn.jsdelivr.net/gh/hfg-gmuend/openmoji@main",
  "https://cdn.jsdelivr.net/gh/hfg-gmuend/openmoji@latest",
];

// ============ STICKER PACK AUTO-DOWNLOADER ============

// Predefined OpenMoji pack categories
const BUILTIN_STICKER_PACKS = [
  { name: "openmoji-all", query: null, trending: false },
  { name: "smileys",      query: null, trending: false },
  { name: "people",       query: null, trending: false },
  { name: "animals",      query: null, trending: false },
  { name: "food",         query: null, trending: false },
  { name: "travel",       query: null, trending: false },
  { name: "activities",   query: null, trending: false },
  { name: "objects",      query: null, trending: false },
  { name: "symbols",      query: null, trending: false },
  { name: "flags",        query: null, trending: false },
];

const STICKER_DL_LIMIT = 200; // per-category cap (openmoji-all ignores this)

// Fallback packs when OpenMoji index is unreachable
const OPENMOJI_PACKS = {
  "openmoji-all": ["1F600", "1F44D", "2764-FE0F", "1F680", "1F525", "1F389", "1F436", "1F4AF", "1F381", "1F923"],
  smileys:   ["1F600", "1F601", "1F602", "1F603", "1F604", "1F60A", "1F60D", "1F618", "1F61B", "1F914", "1F62D", "1F621", "1F634", "1F631", "1F970"],
  people:    ["1F44D", "1F44E", "1F44F", "1F64F", "1F64C", "1F44C", "270C-FE0F", "1F91D", "1F64B", "1F926"],
  animals:   ["1F436", "1F431", "1F42D", "1F439", "1F430", "1F43B", "1F43C", "1F98A", "1F981", "1F42F", "1F428", "1F437", "1F42E", "1F984", "1F99C"],
  food:      ["1F34E", "1F34F", "1F355", "1F354", "1F35F", "1F354", "1F36A", "1F370", "1F37A", "2615"],
  travel:    ["1F697", "1F68C", "1F695", "1F6F5", "1F682", "2708-FE0F", "1F6EB", "1F6E5-FE0F", "1F3D6-FE0F", "1F3D4-FE0F"],
  activities:["26BD", "1F3C0", "1F3BE", "1F3B3", "1F3AF", "1F3AE", "1F3B2", "1F3B8", "1F3A4", "1F3AD"],
  objects:   ["1F4F1", "1F4BB", "1F5A5-FE0F", "2328-FE0F", "1F5B1-FE0F", "1F4A1", "1F4A3", "1F50B", "1F50C", "1F4E6"],
  symbols:   ["2764-FE0F", "1F496", "1F49B", "1F49A", "1F499", "1F49C", "1F5A4", "2714-FE0F", "274C", "1F4AF"],
  flags:     ["1F1EE-1F1F9", "1F1FA-1F1F8", "1F1EC-1F1E7", "1F1EB-1F1F7", "1F1E9-1F1EA", "1F1EA-1F1F8", "1F1EF-1F1F5", "1F1E8-1F1F3"]
};

let openmojiIndexCache = null;

function normalizeOpenMojiGroup(value) {
  return String(value || "")
    .toLowerCase()
    .trim()
    .replace(/\s*&\s*/g, "-")
    .replace(/\s+/g, "-");
}

function openMojiCodeCandidates(hexcode) {
  const cp = String(hexcode || "")
    .toUpperCase()
    .trim()
    .replace(/\s+/g, "-");
  if (!cp) return [];
  const out = [cp];
  if (cp.includes("-FE0F")) out.push(cp.replace(/-FE0F/g, ""));
  return Array.from(new Set(out));
}

async function loadOpenMojiIndex() {
  if (openmojiIndexCache) return openmojiIndexCache;
  let lastErr = null;
  for (const indexUrl of OPENMOJI_INDEX_URLS) {
    try {
      const resp = await axios.get(indexUrl, {
        timeout: 20000,
        headers: { "User-Agent": "WhatsApp-Wap-Client/1.0" },
      });
      const data = Array.isArray(resp.data) ? resp.data : [];
      openmojiIndexCache = data
        .filter((e) => e && typeof e.hexcode === "string")
        .map((e) => ({
          hexcode: String(e.hexcode).toUpperCase().trim(),
          group: normalizeOpenMojiGroup(e.group),
        }));
      logger.info(`[Stickers] OpenMoji index loaded from ${indexUrl}`);
      return openmojiIndexCache;
    } catch (e) {
      lastErr = e;
    }
  }
  logger.warn(`[Stickers] OpenMoji index unavailable on all mirrors: ${lastErr?.message || "unknown error"}`);
  openmojiIndexCache = [];
  return openmojiIndexCache;
}

function getOpenMojiImageCandidates(hexcode) {
  const out = [];
  const cps = openMojiCodeCandidates(hexcode);
  for (const cp of cps) {
    for (const base of OPENMOJI_ASSET_BASES) {
      out.push({ url: `${base}/color/72x72/${cp}.png`, type: "png" });
      out.push({ url: `${base}/color/png/72x72/${cp}.png`, type: "png" });
      out.push({ url: `${base}/color/svg/${cp}.svg`, type: "svg" });
    }
  }
  const seen = new Set();
  return out.filter((entry) => {
    if (seen.has(entry.url)) return false;
    seen.add(entry.url);
    return true;
  });
}

function getOpenMojiCodesForPack(packName, entries) {
  const groupMap = {
    smileys: ["smileys-emotion"],
    people: ["people-body"],
    animals: ["animals-nature"],
    food: ["food-drink"],
    travel: ["travel-places"],
    activities: ["activities"],
    objects: ["objects"],
    symbols: ["symbols"],
    flags: ["flags"],
  };
  if (packName === "openmoji-all") {
    return Array.from(new Set(entries.map((e) => e.hexcode)));
  }
  const groups = groupMap[packName] || [];
  if (!groups.length) return [];
  return Array.from(
    new Set(
      entries
        .filter((e) => groups.includes(e.group))
        .map((e) => e.hexcode)
    )
  );
}

// Track ongoing/completed downloads — keyed by pack name (bounded to BUILTIN_STICKER_PACKS)
const stickerDownloadStatus = new Map(); // packName -> { running, done, downloaded, errors }

// Helper: read status safely
function getStickerStatus(name) {
  return stickerDownloadStatus.get(name) || { running: false, done: false, downloaded: 0, errors: 0 };
}

// Download a sticker pack from Giphy into stickers/<packName>/
// Returns { downloaded, skipped, errors, total }
async function downloadStickerPack(packName, query, trending = false, limit = STICKER_DL_LIMIT) {
  const packDir = path.join(STICKERS_DIR, packName);
  try {
    if (!fs.existsSync(packDir)) fs.mkdirSync(packDir, { recursive: true });
  } catch (e) {
    throw new Error(`Cannot create pack dir '${packName}': ${e.message}`);
  }

  async function downloadFromOpenMoji() {
    const entries = await loadOpenMojiIndex();
    let cps = getOpenMojiCodesForPack(packName, entries);
    if (!cps.length) cps = OPENMOJI_PACKS[packName] || OPENMOJI_PACKS["openmoji-all"] || [];
    const selected = packName === "openmoji-all"
      ? cps
      : cps.slice(0, Math.max(1, Math.min(limit, cps.length)));
    let downloaded = 0, skipped = 0, errors = 0;
    for (const cp of selected) {
      const filename = `${cp}.png`;
      const filepath = path.join(packDir, filename);
      if (fs.existsSync(filepath)) { skipped++; continue; }
      try {
        const candidates = getOpenMojiImageCandidates(cp);
        let saved = false;
        let lastInnerErr = null;
        for (const candidate of candidates) {
          try {
            const resp = await axios.get(candidate.url, {
              responseType: "arraybuffer",
              timeout: 20000,
              maxContentLength: 2 * 1024 * 1024,
              maxBodyLength: 2 * 1024 * 1024,
              headers: { "User-Agent": "WhatsApp-Wap-Client/1.0" },
            });
            if (candidate.type === "svg") {
              const pngBuf = await sharp(resp.data).png().toBuffer();
              await fs.promises.writeFile(filepath, pngBuf);
            } else {
              await fs.promises.writeFile(filepath, resp.data);
            }
            downloaded++;
            saved = true;
            break;
          } catch (inner) {
            lastInnerErr = inner;
          }
        }
        if (!saved) {
          errors++;
          const status = lastInnerErr?.response?.status;
          logger.warn(`[Stickers] OpenMoji missing asset for ${cp}${status ? ` (last status ${status})` : ""}`);
        }
      } catch (e) {
        errors++;
        logger.warn(`[Stickers] OpenMoji failed ${cp}.png: ${e.message}`);
      }
    }
    return { downloaded, skipped, errors, total: selected.length };
  }

  return downloadFromOpenMoji();
}

// Auto-sync all builtin packs in background at startup (every app start).
// Runs only on Worker #1 (called from onServerListening).
async function autoDownloadStickerPacks() {
  try {
    let existingCount = 0;
    try {
      existingCount = fs.readdirSync(STICKERS_DIR).filter(n => {
        try { return fs.statSync(path.join(STICKERS_DIR, n)).isDirectory(); } catch { return false; }
      }).length;
    } catch { /* unreadable dir — continue anyway */ }

    if (existingCount > 0) {
      logger.info(`[Stickers] Found ${existingCount} local pack(s) — startup sync from OpenMoji (missing stickers only)...`);
    } else {
      logger.info("[Stickers] No local packs found — startup full download from OpenMoji...");
    }

    for (const pack of BUILTIN_STICKER_PACKS) {
      // Skip if already in progress (shouldn't happen at startup, but be safe)
      if (getStickerStatus(pack.name).running) continue;

      stickerDownloadStatus.set(pack.name, { running: true, done: false, downloaded: 0, errors: 0 });
      try {
        const r = await downloadStickerPack(pack.name, pack.query, pack.trending);
        stickerDownloadStatus.set(pack.name, { running: false, done: true, downloaded: r.downloaded, errors: r.errors });
        logger.info(`[Stickers] '${pack.name}': +${r.downloaded} new, ${r.skipped} existing, ${r.errors} errors`);
        if (r.downloaded > 0) await new Promise(resolve => setTimeout(resolve, 1200)); // rate-limit courtesy
      } catch (e) {
        stickerDownloadStatus.set(pack.name, { running: false, done: false, downloaded: 0, errors: 1 });
        logger.error(`[Stickers] Failed pack '${pack.name}': ${e.message}`);
      }
    }
    logger.info("[Stickers] Auto-download complete");
  } catch (e) {
    logger.error("[Stickers] autoDownloadStickerPacks error:", e.message);
  }
}

// Pre-convert video to 3GP for Symbian (runs in background)
async function preConvertVideo(messageId, videoBuffer) {
  const outputPath = path.join(MEDIA_CACHE_DIR, `${messageId}.3gp`);

  // Skip if already converted
  if (fs.existsSync(outputPath)) {
    console.log(`[PreConvert] Video ${messageId} already cached`);
    return outputPath;
  }

  const tempInput = safeTempPath(`preconv_video_${messageId}.mp4`);

  try {
    await fs.promises.writeFile(tempInput, videoBuffer);

    await new Promise((resolve, reject) => {
      const ffmpegPath = ffmpeg;
      const process = spawn(ffmpegPath, [
        '-i', tempInput,
        '-y',
        '-c:v', 'h263',
        '-s', '176x144',
        '-r', '15',
        '-b:v', '64k',
        '-c:a', 'libopencore_amrnb',
        '-ar', '8000',
        '-ac', '1',
        '-b:a', '12.2k',
        outputPath
      ]);

      let stderr = '';
      process.stderr.on('data', (data) => { stderr += data.toString(); });
      process.on('close', (code) => {
        if (code === 0) resolve();
        else reject(new Error(`FFmpeg 3GP preconvert failed: ${stderr.slice(-200)}`));
      });
    });

    console.log(`[PreConvert] Video ${messageId} converted to 3GP`);
    return outputPath;
  } catch (error) {
    console.error(`[PreConvert] Video conversion failed:`, error.message);
    return null;
  } finally {
    try { await fs.promises.unlink(tempInput); } catch (e) { }
  }
}

// Pre-convert audio to MP3 for Symbian (runs in background)
async function preConvertAudio(messageId, audioBuffer) {
  const outputPath = path.join(MEDIA_CACHE_DIR, `${messageId}.mp3`);

  // Skip if already converted
  if (fs.existsSync(outputPath)) {
    console.log(`[PreConvert] Audio ${messageId} already cached`);
    return outputPath;
  }

  const tempInput = safeTempPath(`preconv_audio_${messageId}.ogg`);

  try {
    await fs.promises.writeFile(tempInput, audioBuffer);

    await new Promise((resolve, reject) => {
      const ffmpegPath = ffmpeg;
      const process = spawn(ffmpegPath, [
        '-i', tempInput,
        '-y',
        '-c:a', 'libmp3lame',
        '-ar', '22050',
        '-ac', '1',
        '-b:a', '64k',
        outputPath
      ]);

      let stderr = '';
      process.stderr.on('data', (data) => { stderr += data.toString(); });
      process.on('close', (code) => {
        if (code === 0) resolve();
        else reject(new Error(`FFmpeg MP3 preconvert failed: ${stderr.slice(-200)}`));
      });
    });

    console.log(`[PreConvert] Audio ${messageId} converted to MP3`);
    return outputPath;
  } catch (error) {
    console.error(`[PreConvert] Audio conversion failed:`, error.message);
    return null;
  } finally {
    try { await fs.promises.unlink(tempInput); } catch (e) { }
  }
}

// Check if pre-converted media exists
// In-memory cache of known converted files — avoids O(1) fs.existsSync syscall per request
const convertedMediaCache = new Set();
// Build initial cache from disk (one-time O(F) scan at startup)
try {
  if (fs.existsSync(MEDIA_CACHE_DIR)) {
    for (const f of fs.readdirSync(MEDIA_CACHE_DIR)) {
      convertedMediaCache.add(f);
    }
  }
} catch (e) { /* ignore */ }

function getPreConvertedPath(messageId, format) {
  const fileName = `${messageId}.${format}`;
  // O(1) Set check instead of filesystem syscall
  if (convertedMediaCache.has(fileName)) {
    const filePath = path.join(MEDIA_CACHE_DIR, fileName);
    // Verify file still exists (rare edge case: manual deletion)
    if (fs.existsSync(filePath)) return filePath;
    convertedMediaCache.delete(fileName);
  }
  return null;
}

function cacheConvertedMedia(messageId, format, sourcePath) {
  const fileName = `${messageId}.${format}`;
  const destPath = path.join(MEDIA_CACHE_DIR, fileName);
  try {
    fs.copyFileSync(sourcePath, destPath);
    convertedMediaCache.add(fileName);
  } catch (e) { /* ignore */ }
}

// Extract frames from video at 1 FPS
async function extractVideoFrames(videoBuffer, messageId) {
  const framesDir = path.join(VIDEO_FRAMES_DIR, messageId);

  // Check if frames already exist
  if (fs.existsSync(framesDir)) {
    const existingFrames = fs.readdirSync(framesDir).filter(f => f.endsWith('.png'));
    if (existingFrames.length > 0) {
      console.log(`Using cached frames for ${messageId}: ${existingFrames.length} frames`);
      return { frameCount: existingFrames.length, framesDir };
    }
  }

  // Create frames directory (mkdirSync with recursive is safe even if it exists)
  try {
    fs.mkdirSync(framesDir, { recursive: true });
  } catch (e) {
    throw new Error(`Cannot create frames dir for ${messageId}: ${e.message}`);
  }

  const id = `${messageId}_${Date.now()}`;
  const tempVideoPath = safeTempPath(`video_frames_${id}.mp4`);
  const framePattern = path.join(framesDir, 'frame_%04d.png');

  try {
    await fs.promises.writeFile(tempVideoPath, videoBuffer);
    console.log(`Extracting frames from video ${messageId} at 1 FPS...`);

    await new Promise((resolve, reject) => {
      const proc = spawn(ffmpeg, [
        '-i', tempVideoPath,
        '-vf', 'fps=1',
        '-s', '128x128',
        '-q:v', '2',
        framePattern
      ]);
      let stderr = '';
      proc.stderr.on('data', d => { stderr += d.toString(); });
      proc.on('error', reject);
      proc.on('close', code => code === 0 ? resolve() : reject(new Error(`FFmpeg frames failed (${code}): ${stderr.slice(-200)}`)));
    });

    const frames = await fs.promises.readdir(framesDir);
    const pngFrames = frames.filter(f => f.endsWith('.png'));
    console.log(`Extracted ${pngFrames.length} frames from video ${messageId}`);

    return { frameCount: pngFrames.length, framesDir };
  } catch (error) {
    console.error('Frame extraction error:', error.message);
    throw error;
  } finally {
    unlinkSilent(tempVideoPath);
  }
}

// Clean up old video frames (older than 1 hour)
function cleanupOldVideoFrames() {
  try {
    if (!fs.existsSync(VIDEO_FRAMES_DIR)) return;

    const oneHourAgo = Date.now() - (60 * 60 * 1000);
    const dirs = fs.readdirSync(VIDEO_FRAMES_DIR);

    for (const dir of dirs) {
      const dirPath = path.join(VIDEO_FRAMES_DIR, dir);
      const stats = fs.statSync(dirPath);

      if (stats.isDirectory() && stats.mtimeMs < oneHourAgo) {
        console.log(`Cleaning up old video frames: ${dir}`);
        fs.rmSync(dirPath, { recursive: true, force: true });
      }
    }
  } catch (error) {
    console.error('Error cleaning up video frames:', error);
  }
}

// Run cleanup every 30 minutes
setInterval(cleanupOldVideoFrames, 30 * 60 * 1000);

// ============ TEXT-TO-SPEECH ============
// Local TTS using espeak (English and Italian, offline)
async function textToSpeech(text, language = 'en') {
  try {
    console.log(`TTS request: "${text.substring(0, 50)}..." (language: ${language})`);

    if (!ttsEnabled) {
      throw new Error('Local TTS not available. Install espeak: sudo apt-get install espeak');
    }

    // Support only English and Italian
    if (language !== 'en' && language !== 'it') {
      console.log(`⚠ Only English (en) and Italian (it) supported. Using English for ${language}.`);
      language = 'en';
    }

    return await textToSpeechLocal(text, language);
  } catch (error) {
    console.error('TTS conversion error:', error.message);
    throw new Error(`TTS conversion failed: ${error.message}`);
  }
}

// Local TTS using espeak (Raspberry Pi compatible, English and Italian, offline)
async function textToSpeechLocal(text, language = 'en') {
  const id = `${Date.now()}_${Math.random().toString(36).slice(2, 6)}`;
  const tempWav = safeTempPath(`espeak_${id}.wav`);

  try {
    const langName = language === 'it' ? 'Italian' : 'English';
    console.log(`Generating speech with espeak (${langName}, local, offline)...`);

    await new Promise((resolve, reject) => {
      const espeak = spawn('espeak', [
        '-v', language,
        '-s', '150',
        '-a', '200',
        '-w', tempWav,
        text
      ]);
      let stderr = '';
      espeak.stderr.on('data', d => { stderr += d.toString(); });
      espeak.on('error', err => reject(new Error(`espeak execution failed: ${err.message}`)));
      espeak.on('close', code => code === 0 ? resolve() : reject(new Error(`espeak failed (${code}): ${stderr.slice(-200)}`)));
    });

    let wavBuffer;
    try {
      wavBuffer = await fs.promises.readFile(tempWav);
    } catch (e) {
      throw new Error(`espeak produced no output: ${e.message}`);
    }
    console.log(`✓ Generated ${wavBuffer.length} bytes of audio (WAV)`);
    return wavBuffer;
  } catch (error) {
    console.error('espeak TTS error:', error.message);
    throw error;
  } finally {
    unlinkSilent(tempWav);
  }
}

// Google TTS (for non-English languages or fallback)
async function textToSpeechGoogle(text, language = 'en') {
  try {
    // Google Translate TTS API endpoint
    const ttsUrl = `https://translate.google.com/translate_tts`;

    // Split text into chunks if longer than 200 characters (Google TTS limit)
    const maxLength = 200;
    const chunks = [];

    if (text.length <= maxLength) {
      chunks.push(text);
    } else {
      // Split by sentences
      const sentences = text.match(/[^.!?]+[.!?]+/g) || [text];
      let currentChunk = '';

      for (const sentence of sentences) {
        if ((currentChunk + sentence).length <= maxLength) {
          currentChunk += sentence;
        } else {
          if (currentChunk) chunks.push(currentChunk.trim());
          currentChunk = sentence;
        }
      }
      if (currentChunk) chunks.push(currentChunk.trim());
    }

    console.log(`Split into ${chunks.length} chunk(s) for Google TTS`);

    // Fetch audio for each chunk
    const audioBuffers = [];
    for (let i = 0; i < chunks.length; i++) {
      const chunk = chunks[i];
      console.log(`Fetching Google TTS audio for chunk ${i + 1}/${chunks.length}`);

      const response = await axios.get(ttsUrl, {
        params: {
          ie: 'UTF-8',
          tl: language,
          client: 'tw-ob',
          q: chunk,
          textlen: chunk.length
        },
        responseType: 'arraybuffer',
        headers: {
          'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
          'Referer': 'https://translate.google.com/'
        },
        timeout: 30000, // 30 second timeout
        maxContentLength: 10 * 1024 * 1024, // 10MB max
        maxBodyLength: 10 * 1024 * 1024
      });

      audioBuffers.push(Buffer.from(response.data));
    }

    // Concatenate audio buffers if multiple chunks
    if (audioBuffers.length === 1) {
      return audioBuffers[0];
    } else {
      // Simple concatenation works for MP3 files
      return Buffer.concat(audioBuffers);
    }
  } catch (error) {
    console.error('Google TTS error:', error.message);
    throw error;
  }
}

// Helper function to convert Float32Array audio to WAV buffer
async function convertToWav(audioData, samplingRate = 16000) {
  // Create WAV header
  const numChannels = 1;
  const bitsPerSample = 16;
  const byteRate = samplingRate * numChannels * bitsPerSample / 8;
  const blockAlign = numChannels * bitsPerSample / 8;
  const dataSize = audioData.length * 2; // 16-bit = 2 bytes per sample

  const buffer = Buffer.alloc(44 + dataSize);

  // RIFF header
  buffer.write('RIFF', 0);
  buffer.writeUInt32LE(36 + dataSize, 4);
  buffer.write('WAVE', 8);

  // fmt chunk
  buffer.write('fmt ', 12);
  buffer.writeUInt32LE(16, 16); // fmt chunk size
  buffer.writeUInt16LE(1, 20); // audio format (1 = PCM)
  buffer.writeUInt16LE(numChannels, 22);
  buffer.writeUInt32LE(samplingRate, 24);
  buffer.writeUInt32LE(byteRate, 28);
  buffer.writeUInt16LE(blockAlign, 32);
  buffer.writeUInt16LE(bitsPerSample, 34);

  // data chunk
  buffer.write('data', 36);
  buffer.writeUInt32LE(dataSize, 40);

  // Convert float32 to int16
  for (let i = 0; i < audioData.length; i++) {
    const sample = Math.max(-1, Math.min(1, audioData[i]));
    const int16 = sample < 0 ? sample * 0x8000 : sample * 0x7FFF;
    buffer.writeInt16LE(int16, 44 + i * 2);
  }

  return buffer;
}

// ============ WAP PUSH NOTIFICATION HELPER ============
/**
 * Sends a WAP Push notification to the specified phone number
 * @param {string} phoneNumber - Recipient phone number (e.g., "391234567890")
 * @param {string} text - Notification text content (max 100 chars recommended)
 * @param {string} wmlPath - Relative WML path (e.g., "/wml/chat.wml?jid=...")
 * @param {string} siAction - Signal action type (default: "signal-high")
 * @returns {Promise<boolean>} - True if notification sent successfully
 */
async function sendWAPPushNotification(phoneNumber, text, wmlPath, siAction = 'signal-high', expireMs = 120000) {
  try {
    const WAP_PUSH_BASE_URL = process.env.WAP_PUSH_BASE_URL || '';
    if (!WAP_PUSH_BASE_URL) { logger.warn('WAP_PUSH_BASE_URL not configured — skipping WAP Push'); return false; }
    // WAP_SERVER_BASE must be the public URL reachable by the phone (not 127.0.0.1)
    const WAP_SERVER_BASE = process.env.WAP_SERVER_BASE
      || `${HTTPS_ENABLED ? 'https' : 'http'}://${HTTPS_ENABLED ? HTTPS_DOMAIN : '127.0.0.1'}:${HTTPS_ENABLED ? HTTPS_PORT : port}`;
    const AUTH = process.env.WAP_PUSH_AUTH || '';

    const fullWMLURL = `${WAP_SERVER_BASE}${wmlPath}`;
    const truncatedText = text.length > 100 ? text.substring(0, 97) + '...' : text;

    // Genera WAPSIID univoco
    const wapsiid = generateWAPSIID();

    // Funzione per formato locale ISO
    const toLocalISO = (date) => {
      const pad = (n) => n.toString().padStart(2, '0');
      return `${date.getFullYear()}-${pad(date.getMonth() + 1)}-${pad(date.getDate())}T${pad(date.getHours())}:${pad(date.getMinutes())}:${pad(date.getSeconds())}Z`;
    };

    const now = new Date();
    const created = toLocalISO(now);

    // Build params — expiration is optional
    const params = new URLSearchParams({
      PhoneNumber: phoneNumber,
      WAPURL: fullWMLURL,
      Text: truncatedText,
      WAPSIACTION: siAction,
      WAPSIID: wapsiid,
      WAPSICREATED: created
    });

    // Only add expiration if enabled (expireMs > 0)
    if (expireMs > 0) {
      const expireDate = new Date(now.getTime() + expireMs);
      params.set('WAPSIEXPIRES', toLocalISO(expireDate));
    }

    // Invia WAP Push
    const response = await axios.get(`${WAP_PUSH_BASE_URL}?${params.toString()}`, {
      headers: {
        'Authorization': AUTH,
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
        'Accept-Language': 'it-IT,it;q=0.5',
        'Referer': WAP_PUSH_BASE_URL
      },
      timeout: 10000,
      maxRedirects: 5
    });

    if (response.status === 200) {
      logger.info(`✓ WAP Push sent to ${phoneNumber}: "${truncatedText}" [ID: ${wapsiid}, Expire: ${expireMs > 0 ? expireMs + 'ms' : 'none'}]`);

      return { success: true, wapsiid };
    } else {
      logger.warn(`⚠ WAP Push responded with status ${response.status}`);
      return { success: false };
    }
  } catch (error) {
    logger.error(`❌ WAP Push notification failed: ${error.message}`);
    return { success: false, error: error.message };
  }
}


function scheduleWAPDelete(phoneNumber, wapsiid, expireMinutes) {
  const deleteDelayMs = expireMinutes * 60 * 1000 + 5000; // +5 secondi di buffer

  const timeoutId = setTimeout(async () => {
    try {
      logger.info(`🗑️ Sending WAP DELETE for ID: ${wapsiid}`);
      await sendWAPDelete(phoneNumber, wapsiid);
      pendingDeletes.delete(wapsiid);
    } catch (error) {
      logger.error(`❌ WAP DELETE failed for ${wapsiid}: ${error.message}`);
    }
  }, deleteDelayMs);

  // Salva il timeout per eventuale cancellazione
  pendingDeletes.set(wapsiid, { timeoutId, phoneNumber, scheduledFor: new Date(Date.now() + deleteDelayMs) });

  logger.info(`⏰ DELETE scheduled for ${wapsiid} in ${expireMinutes} minutes`);
}

/**
 * Invia la richiesta di DELETE per un WAPSIID specifico
 */
async function sendWAPDelete(phoneNumber, wapsiid) {
  try {
    const WAP_PUSH_BASE_URL = process.env.WAP_PUSH_BASE_URL || '';
    if (!WAP_PUSH_BASE_URL) { logger.warn('WAP_PUSH_BASE_URL not configured — skipping WAP Push delete'); return false; }
    const AUTH = process.env.WAP_PUSH_AUTH || '';

    const params = new URLSearchParams({
  
      PhoneNumber: phoneNumber,
      WAPURL: process.env.WAP_SERVER_BASE || `${HTTPS_ENABLED ? 'https' : 'http'}://${HTTPS_ENABLED ? HTTPS_DOMAIN : '127.0.0.1'}:${HTTPS_ENABLED ? HTTPS_PORT : port}`,
      Text: 'Delete Notification',   // Testo vuoto per delete
      WAPSIACTION: 'delete',
      WAPSIID: wapsiid
    
    });

    const response = await axios.get(`${WAP_PUSH_BASE_URL}?${params.toString()}`, {
      headers: {
        'Authorization': AUTH,
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
        'Accept-Language': 'it-IT,it;q=0.5',
        'Referer': WAP_PUSH_BASE_URL
      },
      timeout: 10000,
      maxRedirects: 5
    });

    if (response.status === 200) {
      logger.info(`✓ WAP DELETE sent successfully for ID: ${wapsiid}`);
      return true;
    } else {
      logger.warn(`⚠ WAP DELETE responded with status ${response.status}`);
      return false;
    }
  } catch (error) {
    logger.error(`❌ WAP DELETE failed: ${error.message}`);
    return false;
  }
}

/**
 * Manages WAP Push notification history with a 30-message limit.
 * When a new notification is added and the limit is exceeded,
 * the oldest notification is automatically deleted from the device.
 * @param {string} phoneNumber - Recipient phone number
 * @param {string} wapsiid - WAP Push notification ID
 * @param {string} text - Notification text
 * @param {Date} timestamp - Notification timestamp
 */
async function manageWAPPushHistory(phoneNumber, wapsiid, text, timestamp) {
  const MAX_NOTIFICATIONS = userSettings.wapPushHistoryLimit || 30;

  // Add new notification to history
  wapPushHistory.push({
    wapsiid,
    phoneNumber,
    text,
    timestamp
  });

  // If we exceed the limit, delete the oldest notification
  if (wapPushHistory.length > MAX_NOTIFICATIONS) {
    const oldest = wapPushHistory.shift(); // Remove oldest from history

    // Send DELETE command to remove the notification from the device
    try {
      logger.info(`🗑️ History limit reached (${MAX_NOTIFICATIONS}), deleting oldest notification ID: ${oldest.wapsiid}`);
      await sendWAPDelete(oldest.phoneNumber, oldest.wapsiid);

      // Also cancel any scheduled auto-delete for this notification
      const pending = pendingDeletes.get(oldest.wapsiid);
      if (pending) {
        clearTimeout(pending.timeoutId);
        pendingDeletes.delete(oldest.wapsiid);
      }
    } catch (error) {
      logger.error(`❌ Failed to delete oldest notification ${oldest.wapsiid}: ${error.message}`);
    }
  }

  logger.info(`📊 WAP Push history: ${wapPushHistory.length}/${MAX_NOTIFICATIONS} notifications`);
}

/**
 * Cancella un delete schedulato (se serve annullare prima dell'expire)
 */
function cancelScheduledDelete(wapsiid) {
  const pending = pendingDeletes.get(wapsiid);
  if (pending) {
    clearTimeout(pending.timeoutId);
    pendingDeletes.delete(wapsiid);
    logger.info(`❌ Cancelled scheduled DELETE for ${wapsiid}`);
    return true;
  }
  return false;
}

/**
 * Ottieni tutti i delete pendenti (per debug/monitoring)
 */
function getPendingDeletes() {
  return Array.from(pendingDeletes.entries()).map(([wapsiid, data]) => ({
    wapsiid,
    phoneNumber: data.phoneNumber,
    scheduledFor: data.scheduledFor
  }));
}


// Helper: silently delete a file, ignoring ENOENT (used in finally blocks)
async function unlinkSilent(filePath) {
  try { await fs.promises.unlink(filePath); } catch { /* ignore */ }
}

// Helper function to concatenate multiple audio files using FFmpeg
async function concatenateAudioFiles(audioBuffers) {
  const id = `${Date.now()}_${Math.random().toString(36).slice(2, 7)}`;
  const tempFiles = [];
  const tempOutput = safeTempPath(`concat_out_${id}.wav`);
  const concatList = safeTempPath(`concat_list_${id}.txt`);

  try {
    for (let i = 0; i < audioBuffers.length; i++) {
      const tempFile = safeTempPath(`concat_chunk_${id}_${i}.wav`);
      await fs.promises.writeFile(tempFile, audioBuffers[i]);
      tempFiles.push(tempFile);
    }

    const listContent = tempFiles.map(f => `file '${f}'`).join('\n');
    await fs.promises.writeFile(concatList, listContent);

    await new Promise((resolve, reject) => {
      const proc = spawn(ffmpeg, ['-f', 'concat', '-safe', '0', '-i', concatList, '-c', 'copy', '-y', tempOutput]);
      let stderr = '';
      proc.stderr.on('data', d => { stderr += d.toString(); });
      proc.on('error', reject);
      proc.on('close', code => code === 0 ? resolve() : reject(new Error(`FFmpeg concat failed (${code}): ${stderr.slice(-200)}`)));
    });

    let concatenated;
    try {
      concatenated = await fs.promises.readFile(tempOutput);
    } catch (e) {
      throw new Error(`FFmpeg concat produced no output: ${e.message}`);
    }
    return concatenated;
  } catch (error) {
    console.error('Audio concatenation error:', error.message);
    throw error;
  } finally {
    for (const f of [...tempFiles, concatList, tempOutput]) unlinkSilent(f);
  }
}

// Helper function to convert WAV to OGG Opus format
async function convertWavToOgg(wavBuffer) {
  const id = `${Date.now()}_${Math.random().toString(36).slice(2, 7)}`;
  const tempWav = safeTempPath(`tts_in_${id}.wav`);
  const tempOgg = safeTempPath(`tts_out_${id}.ogg`);

  try {
    await fs.promises.writeFile(tempWav, wavBuffer);

    await new Promise((resolve, reject) => {
      const proc = spawn(ffmpeg, [
        '-i', tempWav,
        '-c:a', 'libopus',
        '-b:a', '64k',
        '-vbr', 'on',
        '-compression_level', '10',
        '-frame_duration', '60',
        '-application', 'voip',
        '-y', tempOgg
      ]);
      let stderr = '';
      proc.stderr.on('data', d => { stderr += d.toString(); });
      proc.on('error', reject);
      proc.on('close', code => code === 0 ? resolve() : reject(new Error(`FFmpeg OGG failed (${code}): ${stderr.slice(-200)}`)));
    });

    let oggBuffer;
    try {
      oggBuffer = await fs.promises.readFile(tempOgg);
    } catch (e) {
      throw new Error(`FFmpeg OGG produced no output: ${e.message}`);
    }
    return oggBuffer;
  } catch (error) {
    console.error('WAV to OGG conversion error:', error.message);
    throw error;
  } finally {
    unlinkSilent(tempWav);
    unlinkSilent(tempOgg);
  }
}

const app = express();
// Trust proxy — required when behind reverse proxy (nginx, Cloudflare, Opera Mini proxy).
// Fixes express-rate-limit ERR_ERL_UNEXPECTED_X_FORWARDED_FOR validation error.
app.set('trust proxy', 1);
const NODE_ENV = process.env.NODE_ENV || 'development';
const port = Number.parseInt(process.env.PORT || '3500', 10) || 3500;
const isDev = NODE_ENV !== "production";

// ============ HTTPS / LET'S ENCRYPT CONFIG ============
const HTTPS_ENABLED = ['1', 'true', 'yes', 'on'].includes((process.env.HTTPS_ENABLED || 'false').toLowerCase());
const HTTPS_DOMAIN = process.env.HTTPS_DOMAIN || 'example.com';
const HTTPS_EMAIL = process.env.HTTPS_EMAIL || 'admin@example.com';
const HTTPS_PORT = Number.parseInt(process.env.HTTPS_PORT || '443', 10) || 443;
const HTTPS_CERTS_DIR = process.env.HTTPS_CERTS_DIR || path.join(dirname(fileURLToPath(import.meta.url)), 'certs');
const WA_PHONE_NUMBER = (process.env.WA_PHONE_NUMBER || '').replace(/\D/g, '');
const AUTH_ENABLED = !['0', 'false', 'no', 'off'].includes((process.env.AUTH_ENABLED || 'true').toLowerCase());
// WAP Push is now controlled via userSettings.wapPushEnabled (runtime toggle from settings page)
const MARKUP_MODE = (() => {
  const m = (process.env.MARKUP_MODE || 'wml').toLowerCase();
  if (['wml', 'xhtml', 'html5'].includes(m)) return m;
  console.warn(`[env] Invalid MARKUP_MODE="${process.env.MARKUP_MODE}", falling back to "wml"`);
  return 'wml';
})();
const UPLOAD_MARKUP_MODE = (() => {
  const m = (process.env.UPLOAD_MARKUP_MODE || '').toLowerCase();
  if (['wml', 'xhtml', 'html5'].includes(m)) return m;
  // Default: follow MARKUP_MODE when not explicitly set
  if (!process.env.UPLOAD_MARKUP_MODE) return MARKUP_MODE === 'html5' ? 'html5' : MARKUP_MODE;
  console.warn(`[env] Invalid UPLOAD_MARKUP_MODE="${process.env.UPLOAD_MARKUP_MODE}", falling back to MARKUP_MODE`);
  return MARKUP_MODE;
})();
let sock = null;

// ============ PRODUCTION-GRADE PERFORMANCE MONITORING ============
const performanceMetrics = {
  requests: { total: 0, success: 0, errors: 0 },
  responseTime: { total: 0, count: 0, min: Infinity, max: 0 },
  cache: { hits: 0, misses: 0 },
  startTime: Date.now(),

  recordRequest(success, responseTime) {
    this.requests.total++;
    if (success) this.requests.success++;
    else this.requests.errors++;

    this.responseTime.total += responseTime;
    this.responseTime.count++;
    this.responseTime.min = Math.min(this.responseTime.min, responseTime);
    this.responseTime.max = Math.max(this.responseTime.max, responseTime);
  },

  getStats() {
    const uptime = Date.now() - this.startTime;
    const avgResponseTime = this.responseTime.count > 0
      ? (this.responseTime.total / this.responseTime.count).toFixed(2)
      : 0;
    const successRate = this.requests.total > 0
      ? ((this.requests.success / this.requests.total) * 100).toFixed(2)
      : 100;
    const cacheHitRate = (this.cache.hits + this.cache.misses) > 0
      ? ((this.cache.hits / (this.cache.hits + this.cache.misses)) * 100).toFixed(2)
      : 0;

    return {
      uptime: `${Math.floor(uptime / 1000)} seconds`,
      requests: this.requests,
      responseTime: {
        avg: `${avgResponseTime}ms`,
        min: `${this.responseTime.min === Infinity ? 0 : this.responseTime.min}ms`,
        max: `${this.responseTime.max}ms`
      },
      successRate: `${successRate}%`,
      cache: {
        ...this.cache,
        hitRate: `${cacheHitRate}%`
      },
      memory: {
        rss: `${(process.memoryUsage().rss / 1024 / 1024).toFixed(2)} MB`,
        heapUsed: `${(process.memoryUsage().heapUsed / 1024 / 1024).toFixed(2)} MB`
      }
    };
  }
};

// ============ PRODUCTION-GRADE MIDDLEWARE STACK ============

// 0. PERFORMANCE MONITORING - Track response times
app.use((req, res, next) => {
  const startTime = Date.now();
  const originalSend = res.send;

  res.send = function(data) {
    const duration = Date.now() - startTime;

    // Log slow requests (>500ms)
    if (duration > 500) {
      logger.warn(`⚠️  SLOW REQUEST: ${req.method} ${req.path} took ${duration}ms`);
    } else if (duration > 100) {
      logger.info(`⏱️  ${req.method} ${req.path} took ${duration}ms`);
    }

    // Add performance header
    res.setHeader('X-Response-Time', `${duration}ms`);

    return originalSend.call(this, data);
  };

  next();
});

// 1. COMPRESSION - Gzip/Brotli for 70-90% size reduction
app.use(compression({
  level: 6, // Balance between speed and compression
  threshold: 1024, // Only compress responses > 1KB
  filter: (req, res) => {
    if (req.headers['x-no-compression']) return false;
    // O(1) string comparison — skip compression on upload routes to prevent buffering interference
    if (req.url === '/opera/upload' || req.url === '/opera/upload-chunk') return false;
    return compression.filter(req, res);
  }
}));

// 2. SECURITY - Production-grade helmet configuration
app.use(
  helmet({
    contentSecurityPolicy: false, // Disabled for WML compatibility
    frameguard: { action: "deny" },
    hsts: {
      maxAge: 31536000, // 1 year
      includeSubDomains: true,
      preload: true
    },
    noSniff: true,
    xssFilter: true
  })
);

// GLOBAL NO-CACHE — force fresh data on every page load (Opera Mini proxy caching fix)
app.use((req, res, next) => {
  res.setHeader("Cache-Control", "no-cache, no-store, must-revalidate");
  res.setHeader("Pragma", "no-cache");
  res.setHeader("Expires", "0");
  next();
});

// 3. PERFORMANCE TRACKING - Request timing middleware
app.use((req, res, next) => {
  const startTime = Date.now();

  res.on('finish', () => {
    const responseTime = Date.now() - startTime;
    const success = res.statusCode < 400;
    performanceMetrics.recordRequest(success, responseTime);

    // Log slow requests (> 1 second)
    if (responseTime > 1000) {
      logger.warn(`Slow request: ${req.method} ${req.path} - ${responseTime}ms`);
    }
  });

  next();
});

// 4. RATE LIMITING - Advanced protection with different tiers
const apiLimiter = rateLimit({
  windowMs: 15 * 60 * 1000, // 15 minutes
  max: isDev ? 1000 : 100, // API requests per window
  message: 'Too many API requests, please try again later',
  standardHeaders: true,
  legacyHeaders: false,
  skip: (req) => isDev && req.ip === '127.0.0.1' // Skip localhost in dev
});

const wmlLimiter = rateLimit({
  windowMs: 1 * 60 * 1000, // 1 minute
  max: isDev ? 500 : 60, // WML page requests per minute
  message: 'Too many requests, please slow down',
  standardHeaders: true,
  legacyHeaders: false
});

app.use("/api", apiLimiter);
app.use("/wml", wmlLimiter);

// ============ AUTHENTICATION MIDDLEWARE ============
// Protect all WML pages - redirect to QR if not connected
app.use("/wml", (req, res, next) => {
  // Allow access to QR code pages and logout page without authentication
  const publicPages = ['/wml/qr.wml', '/wml/qr-wap.wml', '/wml/qr-text.wml', '/wml/qr-display.wml', '/wml/pairing.wml', '/wml/pairing-request.wml', '/wml/logout.wml', '/wml/logout.confirm.wml'];

  if (publicPages.includes(req.path)) {
    return next();
  }

  // Only redirect if WhatsApp has NEVER been authenticated (no credentials).
  // If credentials exist but connection is temporarily down (reconnecting),
  // let pages through so users see cached data and don't get stuck in redirect loops.
  if (!sock?.authState?.creds) {
    return res.redirect(302, '/wml/qr.wml');
  }

  next();
});
// 5. LOGGING - Production-grade Winston logger
const logger = winston.createLogger({
  level: isDev ? "debug" : "info",
  format: winston.format.combine(
    winston.format.timestamp(),
    winston.format.errors({ stack: true }),
    winston.format.json()
  ),
  transports: [
    new winston.transports.Console({
      format: winston.format.combine(
        winston.format.colorize(),
        winston.format.simple()
      )
    }),
    new winston.transports.File({
      filename: "error.log",
      level: "error",
      maxsize: 5242880, // 5MB
      maxFiles: 5
    }),
    new winston.transports.File({
      filename: "app.log",
      maxsize: 5242880, // 5MB
      maxFiles: 5
    }),
  ],
});

// 6. BODY PARSERS - With size limits for security
app.use(express.urlencoded({
  extended: true,
  limit: '10mb',
  parameterLimit: 1000
}));
app.use(express.json({
  limit: '10mb'
}));

// 7. SESSION MIDDLEWARE
const sessionDbPath = resolveDbPath(
  process.env.SESSION_DB_PATH || path.join(PROJECT_DIR, 'sessions.db'),
  'sessions.db',
  'session'
);
const sessionDb = new Database(sessionDbPath);
app.use(session({
  store: new BetterSqlite3Store({ client: sessionDb, expired: { clear: true, intervalMs: 3600000 } }),
  secret: sessionSecret,
  name: 'sid',           // avoid dot in name — WAP 1.x gateways reject "connect.sid"
  resave: true,          // WAP gateways need consistent Set-Cookie on every response
  saveUninitialized: true, // create session immediately so cookie is sent before login
  rolling: true,         // reset session expiry on every request
  cookie: {
    maxAge: 7 * 24 * 60 * 60 * 1000,
    path: '/',
    httpOnly: false,
    secure: false,
    sameSite: false       // omit SameSite attribute entirely — WAP gateways choke on it
  }
}));

// Strip unknown cookie attributes for WAP 1.x gateways.
// Some gateways reject Set-Cookie headers with attributes they don't understand
// (SameSite, Priority, Partitioned, etc.). We rewrite the header to keep only
// name=value, Path, and Expires — the bare minimum for HTTP/1.0 cookie support.
app.use((_req, res, next) => {
  const origSetHeader = res.setHeader.bind(res);
  res.setHeader = (name, value) => {
    if (name.toLowerCase() === 'set-cookie') {
      const cookies = Array.isArray(value) ? value : [value];
      const cleaned = cookies.map(c => {
        // Keep only: name=value; Path=...; Expires=...
        const parts = c.split(';').map(p => p.trim());
        const keep = [parts[0]]; // name=value
        for (const p of parts.slice(1)) {
          const lower = p.toLowerCase();
          if (lower.startsWith('path=') || lower.startsWith('expires=')) {
            keep.push(p);
          }
        }
        return keep.join('; ');
      });
      return origSetHeader(name, cleaned);
    }
    return origSetHeader(name, value);
  };
  next();
});


// 8. AUTHENTICATION MIDDLEWARE — cookie-based session only
app.use((req, res, next) => {
  // If auth is disabled, allow all requests
  if (!AUTH_ENABLED) return next();

  if (req.path === '/login' || req.path === '/login-error' || req.path === '/login-success' || req.path === '/logout') return next();
  // Health/liveness probes must be unauthenticated for monitoring systems
  if (req.path === '/health' || req.path === '/ready' || req.path === '/live') return next();
  // QR image endpoints are public
  if (req.path === '/api/qr/image' || req.path === '/api/qr/wml-wbmp') return next();
  // Legacy /h/:token path — redirect to home (backwards compat)
  if (req.path.startsWith('/h/')) return res.redirect(302, '/wml/home.wml');

  if (req.session && req.session.authenticated) {
    return next();
  }

  // Serve login page directly
  return sendWml(res, card('login', t('login.title'), `
    <p><b>${t('app_name')}</b></p>
    <p>${t('login.user')}
      <input name="usr" type="text" maxlength="64"/>
    </p>
    <p>${t('login.password')}
      <input name="pw" type="text" maxlength="64"/>
    </p>
    <p>
      <anchor title="${t('login.submit')}">${t('login.submit')}
        <go href="/login" method="post">
          <postfield name="user" value="$(usr)"/>
          <postfield name="password" value="$(pw)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('login.submit')}">
      <go href="/login" method="post">
        <postfield name="user" value="$(usr)"/>
        <postfield name="password" value="$(pw)"/>
      </go>
    </do>
  `));
});

// 9. LANGUAGE MIDDLEWARE — sync language from session cookie
app.use((req, _res, next) => {
  if (req.session?.lang && translations[req.session.lang]) {
    userSettings.defaultLanguage = req.session.lang;
  }
  next();
});

// Storage with better persistence
const storage = new PersistentStorage("./data");
const persistentData = storage.loadAllData();

// Core stores — all Map-based for O(1) get/set/has/delete per key
let messageStore = persistentData.messages;   // Map<messageId, message> — O(1) lookup by ID
let contactStore = persistentData.contacts;   // Map<jid, contact> — O(1) lookup by JID
let chatStore = persistentData.chats;         // Map<chatId, message[]> — O(1) chat lookup, O(M) per-chat scan
let connectionState = "disconnected";

// ============ O(1) LOOKUP INDEXES ============
// Reverse index: messageId → chatJid (avoids O(C*M) nested loops)
const messageToChatIndex = new Map();
// Per-chat message ID sets for O(1) duplicate detection (avoids O(n) .some())
const chatMessageIdSets = new Map();
// Phone number → contact key index for O(1) phone lookups (avoids O(n) scan)
const phoneToContactIndex = new Map();

// Build indexes from existing persistent data
(function buildIndexes() {
  for (const [chatId, messages] of chatStore.entries()) {
    const idSet = new Set();
    for (const msg of messages) {
      if (msg.key?.id) {
        messageToChatIndex.set(msg.key.id, chatId);
        idSet.add(msg.key.id);
      }
    }
    chatMessageIdSets.set(chatId, idSet);
  }
  for (const [key, value] of contactStore.entries()) {
    if (value.phoneNumber) {
      phoneToContactIndex.set(value.phoneNumber, key);
    }
    // Also index the numeric part of the JID
    const numericPart = key.replace(/@.*$/, '');
    if (numericPart) {
      phoneToContactIndex.set(numericPart, key);
    }
  }
})();

// ============ GLOBAL OPTIMIZED HELPERS ============
// Single-pass WML escape (O(L) one pass instead of O(5L) five .replace() chains)
// Strips non-ASCII for WAP 1.0 device compatibility
function escWml(text) {
  return (text || '').replace(/[&<>"'\x00-\x1F\x7F-\uFFFF]/g, c => {
    switch (c) {
      case '&': return '&amp;';
      case '<': return '&lt;';
      case '>': return '&gt;';
      case '"': return '&quot;';
      case "'": return '&apos;';
      default: return '?';
    }
  });
}

// Top-K selection: O(N) instead of O(N log N) full sort for paginated results
function topK(arr, k, compareFn) {
  if (arr.length <= k) return arr.slice().sort(compareFn);
  // Partial selection: maintain a k-size heap
  const heap = arr.slice(0, k);
  heap.sort(compareFn);
  for (let i = k; i < arr.length; i++) {
    if (compareFn(arr[i], heap[k - 1]) < 0) {
      heap[k - 1] = arr[i];
      // Re-insert at correct position (insertion sort on k elements)
      let j = k - 2;
      while (j >= 0 && compareFn(heap[j], heap[j + 1]) > 0) {
        [heap[j], heap[j + 1]] = [heap[j + 1], heap[j]];
        j--;
      }
    }
  }
  return heap;
}

const SUPPORTED_IMAGE_TYPES = new Set(['image/jpeg', 'image/png', 'image/webp', 'image/gif']);

// Single-pass array partition helper (replaces 2x .filter() for JID/LID split)
function partitionByLid(arr) {
  const jid = [], lid = [];
  for (const item of arr) {
    if (item.id.startsWith('lid:')) lid.push(item);
    else jid.push(item);
  }
  return [jid, lid];
}

// Cached message search text: messageId → lowercased searchable text
const messageSearchTextCache = new Map();

function extractInlineTextFromContent(content) {
  if (!content) return "";
  const txt = content.conversation || content.extendedTextMessage?.text || "";
  return typeof txt === "string" ? txt.trim() : "";
}

function stickerDescriptor(stickerMessage) {
  const sizeKb = Math.max(0, Math.round((Number(stickerMessage?.fileLength) || 0) / 1024));
  const animated = !!stickerMessage?.isAnimated;
  const mode = animated ? "anim" : "static";
  const short = sizeKb > 0 ? `[STK ${mode.toUpperCase()} ${sizeKb}KB]` : `[STK ${mode.toUpperCase()}]`;
  const human = sizeKb > 0 ? `Sticker ${mode} ${sizeKb}KB` : `Sticker ${mode}`;
  return { sizeKb, animated, mode, short, human };
}

function stickerTextWithOptionalText(stickerMessage, inlineText = "", shortMode = false) {
  const d = stickerDescriptor(stickerMessage);
  const clean = String(inlineText || "").trim();
  if (!clean) return shortMode ? d.short : d.human;
  const preview = truncate(clean, shortMode ? 28 : 60);
  return shortMode ? `${d.short} + TXT: ${preview}` : `${d.human} + Text: ${preview}`;
}

function getMessageSearchText(msg) {
  const id = msg.key?.id;
  if (id && messageSearchTextCache.has(id)) return messageSearchTextCache.get(id);
  const content = extractMessageContent(msg.message);
  let text = '';
  const inlineText = extractInlineTextFromContent(content);
  if (content?.stickerMessage) text = stickerTextWithOptionalText(content.stickerMessage, inlineText, false);
  else if (content?.conversation) text = content.conversation;
  else if (content?.extendedTextMessage?.text) text = content.extendedTextMessage.text;
  else if (content?.imageMessage) text = '[Image] ' + (content.imageMessage.caption || '');
  else if (content?.videoMessage) text = '[Video] ' + (content.videoMessage.caption || '');
  else if (content?.audioMessage) {
    text = `[Audio ${content.audioMessage.seconds || 0}s]`;
    if (msg.transcription && msg.transcription !== '[Trascrizione fallita]' && msg.transcription !== '[Audio troppo lungo per la trascrizione]') {
      text += ' ' + msg.transcription;
    }
  } else if (content?.documentMessage) text = '[Document] ' + (content.documentMessage.fileName || '');
  else if (content?.locationMessage) text = '[Location]';
  else if (content?.contactMessage) text = '[Contact]';
  const lower = text.toLowerCase();
  if (id) messageSearchTextCache.set(id, lower);
  return lower;
}

// Bound cache size to prevent memory leaks
function trimSearchTextCache() {
  if (messageSearchTextCache.size > 50000) {
    // Remove oldest half
    const entries = messageSearchTextCache.keys();
    let toRemove = Math.floor(messageSearchTextCache.size / 2);
    while (toRemove-- > 0) {
      messageSearchTextCache.delete(entries.next().value);
    }
  }
}

let currentQR ; // Store the current QR code
let currentPairingCode = null; // Store the current pairing code (alternative to QR)
let isFullySynced = persistentData.meta.isFullySynced;

// WAP Push notification history (max 30 messages)
const wapPushHistory = [];

// ============ ULTRA-PERFORMANCE CACHE SYSTEM ============
// Pre-sorted indexes for instant page responses
class PerformanceCache {
  constructor() {
    // Sorted contact list with timestamps (updated only when data changes)
    this.sortedContacts = [];
    this.sortedContactsTimestamp = 0;

    // Sorted chat list with timestamps
    this.sortedChats = [];
    this.sortedChatsTimestamp = 0;

    // Message count per chat (for quick lookups)
    this.chatMessageCounts = new Map();

    // Last message timestamp per chat (for sorting)
    this.chatLastMessageTimestamp = new Map();

    // Contact search index (lowercase names and numbers)
    this.contactSearchIndex = new Map();

    // Cached WML fragments (for pagination)
    this.wmlFragmentCache = new Map();
    this.wmlFragmentCacheTTL = 30000; // 30 seconds

    // Dirty flags
    this.contactsDirty = true;
    this.chatsDirty = true;
  }

  // Mark contacts as dirty (needs re-sort)
  invalidateContacts() {
    this.contactsDirty = true;
    this.sortedContactsTimestamp = Date.now();
  }

  // Mark chats as dirty
  invalidateChats() {
    this.chatsDirty = true;
    this.sortedChatsTimestamp = Date.now();
  }

  // Mark specific chat messages as dirty
  invalidateChatMessages(chatId) {
    const cacheKey = `chat_${chatId}`;
    this.wmlFragmentCache.delete(cacheKey);
  }

  // Clear all WML fragment cache
  clearWMLCache() {
    this.wmlFragmentCache.clear();
  }

  // Get sorted contacts (instant if cache valid)
  getSortedContacts(contactStore, chatStore) {
    if (!this.contactsDirty && this.sortedContacts.length > 0) {
      return this.sortedContacts;
    }

    // Rebuild sorted contacts index
    const contactsWithTimestamp = [];
    for (const contact of contactStore.values()) {
      const messages = chatStore.get(contact.id) || [];
      const lastMessage = messages.length > 0 ? messages[messages.length - 1] : null;
      const timestamp = lastMessage ? Number(lastMessage.messageTimestamp) : 0;

      contactsWithTimestamp.push({
        contact,
        timestamp,
        searchText: `${contact.name || contact.notify || ''} ${contact.id}`.toLowerCase()
      });

      // Update search index
      this.contactSearchIndex.set(contact.id, contactsWithTimestamp[contactsWithTimestamp.length - 1].searchText);
    }

    // Sort once
    contactsWithTimestamp.sort((a, b) => b.timestamp - a.timestamp);

    this.sortedContacts = contactsWithTimestamp;
    this.contactsDirty = false;

    return this.sortedContacts;
  }

  // Get sorted chats (instant if cache valid)
  getSortedChats(chatStore) {
    if (!this.chatsDirty && this.sortedChats.length > 0) {
      return this.sortedChats;
    }

    // Rebuild sorted chats index
    const chatsWithTimestamp = [];
    for (const [chatId, messages] of chatStore.entries()) {
      const lastMessage = messages.length > 0 ? messages[messages.length - 1] : null;
      const timestamp = lastMessage ? Number(lastMessage.messageTimestamp) : 0;

      chatsWithTimestamp.push({
        chatId,
        messages,
        timestamp,
        messageCount: messages.length
      });

      // Update quick lookup maps
      this.chatMessageCounts.set(chatId, messages.length);
      this.chatLastMessageTimestamp.set(chatId, timestamp);
    }

    // Sort once
    chatsWithTimestamp.sort((a, b) => b.timestamp - a.timestamp);

    this.sortedChats = chatsWithTimestamp;
    this.chatsDirty = false;

    return this.sortedChats;
  }

  // Quick pagination (instant - no sorting needed)
  paginateContacts(page, limit, searchFilter = null) {
    const sorted = this.sortedContacts;

    // Filter if needed
    let filtered = sorted;
    if (searchFilter) {
      const searchLower = searchFilter.toLowerCase();
      filtered = sorted.filter(c => c.searchText.includes(searchLower));
    }

    const total = filtered.length;
    const start = (page - 1) * limit;
    const items = filtered.slice(start, start + limit);

    return { items, total, totalPages: Math.ceil(total / limit) };
  }

  // Quick chat pagination
  paginateChats(page, limit, searchFilter = null) {
    const sorted = this.sortedChats;

    // Filter if needed
    let filtered = sorted;
    if (searchFilter) {
      const searchLower = searchFilter.toLowerCase();
      filtered = sorted.filter(c => c.chatId.toLowerCase().includes(searchLower));
    }

    const total = filtered.length;
    const start = (page - 1) * limit;
    const items = filtered.slice(start, start + limit);

    return { items, total, totalPages: Math.ceil(total / limit) };
  }

  // Get cached WML fragment
  getWMLFragment(key) {
    const cached = this.wmlFragmentCache.get(key);
    if (!cached) return null;

    // Check TTL
    if (Date.now() - cached.timestamp > this.wmlFragmentCacheTTL) {
      this.wmlFragmentCache.delete(key);
      return null;
    }

    return cached.html;
  }

  // Set cached WML fragment
  setWMLFragment(key, html) {
    this.wmlFragmentCache.set(key, {
      html,
      timestamp: Date.now()
    });
  }
}

const perfCache = new PerformanceCache();

// Build initial cache on startup for instant first page load
logger.info('🚀 Building performance cache on startup...');
const cacheStart = Date.now();
perfCache.getSortedContacts(contactStore, chatStore);
perfCache.getSortedChats(chatStore);
const cacheTime = Date.now() - cacheStart;
logger.info(`✅ Performance cache built in ${cacheTime}ms - ${contactStore.size} contacts, ${chatStore.size} chats`);
logger.info(`📊 Cache ready: ${perfCache.sortedContacts.length} contacts sorted, ${perfCache.sortedChats.length} chats sorted`);

// ============ QR CODE PERSISTENCE ============
const QR_FILE_PATH = path.join(__dirname, 'auth_info_baileys', 'currentQR.json');

// Save QR code to file
function saveQRToFile(qr) {
  try {
    const qrData = {
      qr: qr,
      timestamp: Date.now()
    };
    fs.writeFileSync(QR_FILE_PATH, JSON.stringify(qrData, null, 2));
    logger.info('QR code saved to file');
  } catch (error) {
    logger.error('Failed to save QR code to file:', error);
  }
}

// Load QR code from file
function loadQRFromFile() {
  try {
    if (fs.existsSync(QR_FILE_PATH)) {
      const data = fs.readFileSync(QR_FILE_PATH, 'utf8');
      const qrData = JSON.parse(data);

      // Check if QR is not older than 5 minutes (QR codes expire)
      const fiveMinutes = 5 * 60 * 1000;
      if (Date.now() - qrData.timestamp < fiveMinutes) {
        logger.info('QR code loaded from file');
        return qrData.qr;
      } else {
        logger.info('Stored QR code expired, removing file');
        fs.unlinkSync(QR_FILE_PATH);
      }
    }
  } catch (error) {
    logger.error('Failed to load QR code from file:', error);
  }
  return null;
}

// Clear QR file
function clearQRFile() {
  try {
    fs.unlinkSync(QR_FILE_PATH);
    logger.info('QR code file cleared');
  } catch (error) {
    if (error.code !== 'ENOENT') logger.error('Failed to clear QR code file:', error);
  }
}
let syncAttempts = persistentData.meta.syncAttempts;
let isConnecting = false; // Prevent race conditions in connection logic

// ============ PRODUCTION-GRADE ADVANCED CACHING SYSTEM ============
// Multi-layer LRU cache with automatic memory management
class ProductionCache {
  constructor(maxSize = 999999999999, ttl = 60000) {
    this.cache = new Map();
    this.maxSize = maxSize;
    this.ttl = ttl;
    this.hits = 0;
    this.misses = 0;
  }

  get(key) {
    const item = this.cache.get(key);

    if (!item) {
      this.misses++;
      performanceMetrics.cache.misses++;
      return null;
    }

    // Check TTL
    if (Date.now() - item.timestamp > this.ttl) {
      this.cache.delete(key);
      this.misses++;
      performanceMetrics.cache.misses++;
      return null;
    }

    // LRU: Move to end (most recently used)
    this.cache.delete(key);
    this.cache.set(key, item);

    this.hits++;
    performanceMetrics.cache.hits++;
    return item.data;
  }

  set(key, data) {
    // Evict oldest if at capacity (LRU)
    if (this.cache.size >= this.maxSize) {
      const firstKey = this.cache.keys().next().value;
      this.cache.delete(firstKey);
    }

    this.cache.set(key, {
      data,
      timestamp: Date.now()
    });
  }

  invalidate(key) {
    if (key) {
      this.cache.delete(key);
    } else {
      this.cache.clear();
    }
  }

  getStats() {
    const total = this.hits + this.misses;
    const hitRate = total > 0 ? ((this.hits / total) * 100).toFixed(2) : 0;

    return {
      size: this.cache.size,
      maxSize: this.maxSize,
      hits: this.hits,
      misses: this.misses,
      hitRate: `${hitRate}%`
    };
  }
}

// Initialize caches optimized for 4GB Raspberry Pi 4
const groupsCache = new ProductionCache(100, 120000); // 100 groups, 2min TTL (4GB RAM optimized)
const contactsCache = new ProductionCache(1000, 600000); // 1000 contacts, 10min TTL (4GB RAM optimized)
const chatsCache = new ProductionCache(200, 300000); // 200 chats, 5min TTL (4GB RAM optimized)
const messagesCache = new ProductionCache(2000, 120000); // 2000 messages, 2min TTL (4GB RAM optimized)

// ============ USER SETTINGS & FAVORITES ============
// Load user settings with defaults (merge saved settings over defaults)
let userSettings = {
  defaultLanguage: 'en',
  defaultImageFormat: 'wbmp',
  defaultVideoFormat: 'wbmp',
  paginationLimit: 10,
  refreshTimerUnits: normalizeWmlRefreshUnits(process.env.WML_REFRESH_TIMER_UNITS || '100'),
  autoRefresh: false,
  showHelp: true,
  ttsEnabled: true,
  favorites: [],
  lastStickerTo: '',
  wapPushPhone: '',
  wapPushEnabled: true,
  wapPushExpireEnabled: true,
  wapPushExpireMs: 120000,       // 2 minutes default
  wapPushDeleteEnabled: true,
  wapPushHistoryEnabled: true,
  wapPushHistoryLimit: 30,
  ...(persistentData.settings || {}),
  // Env var always wins over persisted value
  ...(process.env.WAP_PUSH_PHONE ? { wapPushPhone: process.env.WAP_PUSH_PHONE } : {})
};

// ============ I18N / TRANSLATIONS ============
const __localesDir = path.join(path.dirname(fileURLToPath(import.meta.url)), 'locales');
const translations = {};
try {
  translations.en = JSON.parse(fs.readFileSync(path.join(__localesDir, 'en.json'), 'utf8'));
} catch (e) { translations.en = {}; }
try {
  translations.it = JSON.parse(fs.readFileSync(path.join(__localesDir, 'it.json'), 'utf8'));
} catch (e) { translations.it = {}; }

// Translate a dot-notation key using current UI language
function t(key) {
  const lang = userSettings?.defaultLanguage || 'en';
  const dict = translations[lang] || translations.en || {};
  const keys = key.split('.');
  let val = dict;
  for (const k of keys) {
    if (val && typeof val === 'object') val = val[k];
    else { val = undefined; break; }
  }
  if (val === undefined && lang !== 'en') {
    val = translations.en;
    for (const k of keys) {
      if (val && typeof val === 'object') val = val[k];
      else { val = undefined; break; }
    }
  }
  return typeof val === 'string' ? val : key;
}

// Save settings
function saveSettings() {
  storage.queueSave("settings", userSettings);
}

function getWmlRefreshTimerUnits() {
  return normalizeWmlRefreshUnits(userSettings?.refreshTimerUnits);
}

// Favorite contacts helpers — O(1) Set instead of O(n) Array
const favoritesSet = new Set(userSettings.favorites || []);

function addFavorite(jid) {
  if (!favoritesSet.has(jid)) {
    favoritesSet.add(jid);
    userSettings.favorites = Array.from(favoritesSet);
    saveSettings();
    return true;
  }
  return false;
}

function removeFavorite(jid) {
  if (favoritesSet.has(jid)) {
    favoritesSet.delete(jid);
    userSettings.favorites = Array.from(favoritesSet);
    saveSettings();
    return true;
  }
  return false;
}

function isFavorite(jid) {
  return favoritesSet.has(jid);
}

// ============ UNREAD COUNT CACHE ============
// Per-chat unread counts — O(1) per-chat lookup instead of O(M) filter each time
// Global total is sum of per-chat counts — O(1) read
const perChatUnreadCount = new Map(); // Map<chatId, number>
let cachedUnreadCount = -1; // -1 = needs initial computation

// O(1) per-chat unread lookup; lazy-initializes from O(M) scan on first access
function getChatUnreadCount(chatId) {
  if (perChatUnreadCount.has(chatId)) return perChatUnreadCount.get(chatId);
  // First access — compute once: O(M) where M = messages in this chat
  const msgs = chatStore.get(chatId) || [];
  let count = 0;
  for (const msg of msgs) {
    if (!msg.key.fromMe && !msg.messageStubType && msg.message) count++;
  }
  perChatUnreadCount.set(chatId, count);
  return count;
}

// O(C) initial computation, then O(1) reads via cached total
function getUnreadCount() {
  if (cachedUnreadCount >= 0) return cachedUnreadCount;
  let count = 0;
  for (const chatId of chatStore.keys()) {
    count += getChatUnreadCount(chatId);
  }
  cachedUnreadCount = count;
  return count;
}

function incrementUnreadCount(chatId) {
  if (chatId) perChatUnreadCount.set(chatId, (perChatUnreadCount.get(chatId) || 0) + 1);
  if (cachedUnreadCount >= 0) cachedUnreadCount++;
}
function resetUnreadCount() {
  cachedUnreadCount = -1;
  perChatUnreadCount.clear();
}

// Get recent chats — O(C) single pass with partial sort instead of O(C log C) full sort
function getRecentChats(limit = 3) {
  // Use a min-heap approach: keep only top-K items, O(C * limit) ≈ O(C) for small limit
  const top = [];
  for (const [jid, messages] of chatStore.entries()) {
    if (messages.length > 0) {
      const lastMsg = messages[messages.length - 1];
      const ts = Number(lastMsg.messageTimestamp) || 0;
      if (top.length < limit) {
        top.push({ jid, timestamp: ts, lastMessage: lastMsg });
        if (top.length === limit) top.sort((a, b) => a.timestamp - b.timestamp);
      } else if (ts > top[0].timestamp) {
        top[0] = { jid, timestamp: ts, lastMessage: lastMsg };
        top.sort((a, b) => a.timestamp - b.timestamp);
      }
    }
  }
  top.sort((a, b) => b.timestamp - a.timestamp);
  return top;
}

// Build recent chats WML section
// legacy=true: compact layout for WAP 1.x browsers (shorter names/previews, all in one <p>)
// legacy=false: each chat in its own <p> with longer names/previews
function buildRecentChatsHtml(recentChats, legacy = false) {
  if (recentChats.length === 0) return '';
  let html = `<p><b>${t('home.recent_header')}</b></p>`;

  const formatRecentTime = (timestamp) => {
    if (!timestamp) return '';
    const date = new Date(Number(timestamp) * 1000);
    if (isNaN(date.getTime())) return '';
    const day = date.getDate().toString().padStart(2, '0');
    const month = (date.getMonth() + 1).toString().padStart(2, '0');
    const year = date.getFullYear();
    const hours = date.getHours().toString().padStart(2, '0');
    const mins = date.getMinutes().toString().padStart(2, '0');
    const secs = date.getSeconds().toString().padStart(2, '0');
    return `${day}/${month}/${year} ${hours}:${mins}:${secs}`;
  };

  if (legacy) {
    html += '<p>';
    for (const chat of recentChats) {
      const contact = contactStore.get(chat.jid);
      const name = contact?.name || contact?.notify || jidFriendly(chat.jid);
      const lastText = chat.lastMessage ? (messageText(chat.lastMessage) || '') : '';
      const preview = lastText.length > 16 ? lastText.substring(0, 14) + '..' : lastText;
      const fromMe = chat.lastMessage?.key?.fromMe;
      const dir = fromMe ? 'out' : 'in';
      const ts = formatRecentTime(chat.lastMessage?.messageTimestamp || chat.conversationTimestamp);
      html += `<a href="/wml/chat.wml?jid=${encodeURIComponent(chat.jid)}">${esc(name.substring(0, 13))}</a>`;
      if (preview) html += ` [${dir}] ${esc(preview)}`;
      if (ts) html += ` <small>${ts}</small>`;
      html += '<br/>';
    }
    html += '</p>';
  } else {
    for (const chat of recentChats) {
      const contact = contactStore.get(chat.jid);
      const name = contact?.name || contact?.notify || jidFriendly(chat.jid);
      const lastText = chat.lastMessage ? (messageText(chat.lastMessage) || '') : '';
      const preview = lastText.length > 20 ? lastText.substring(0, 18) + '..' : lastText;
      const fromMe = chat.lastMessage?.key?.fromMe;
      const dir = fromMe ? 'out' : 'in';
      const ts = formatRecentTime(chat.lastMessage?.messageTimestamp || chat.conversationTimestamp);
      const previewStr = preview ? ` [${dir}] ${esc(preview)}` : '';
      const timeStr = ts ? `<br/><small>${ts}</small>` : '';
      html += `<p><a href="/wml/chat.wml?jid=${encodeURIComponent(chat.jid)}">${esc(name.substring(0, 15))}</a>${previewStr}${timeStr}</p>`;
    }
  }
  return html;
}

// WML Constants
const WML_DTD =
  '<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.3//EN" "http://www.wapforum.org/DTD/wml13.dtd">';
const WMLSCRIPT_DTD =
  '<!DOCTYPE wmls PUBLIC "-//WAPFORUM//DTD WMLScript 1.3//EN" "http://www.wapforum.org/DTD/wmls13.dtd">';

// WML Helper Functions
function esc(s = "") {
  return String(s).replace(
    /[&<>"']/g,
    (c) =>
      ({
        "&": "&amp;",
        "<": "&lt;",
        ">": "&gt;",
        '"': "&quot;",
        "'": "&#39;",
      }[c])
  );
}

function saveContacts() {
  storage.queueSave("contacts", contactStore);
}

function saveChats() {
  storage.queueSave("chats", chatStore);
}

function saveMessages() {
  storage.queueSave("messages", messageStore);
}

function saveMeta() {
  const meta = {
    isFullySynced,
    syncAttempts,
    lastSync: new Date().toISOString(),
    contactsCount: contactStore.size,
    chatsCount: chatStore.size,
    messagesCount: messageStore.size,
  };
  storage.queueSave("meta", meta);
}

// Save all persistent data
function saveAll() {
  saveContacts();
  saveChats();
  saveMessages();
  saveMeta();
  // Note: Auth state is automatically managed by Baileys via useMultiFileAuthState
}
// ============ MARKUP MODE TRANSFORMER ============
// Converts WML document strings to XHTML 1.0 Strict or HTML5 via regex transforms.
// Called by sendWml() and sendRawWmlAware() when MARKUP_MODE !== 'wml'.

// XHTML 1.0 compatible CSS — no CSS custom properties (var()), no :root,
// no modern selectors. Maximum compatibility with older browsers (Opera Mini, IE6-8, Symbian).
// WCSS-compatible CSS for XHTML Mobile Profile 1.0 (WAP 2.0 devices)
// Uses only CSS2 subset supported by WCSS: no var(), no :root, no border-radius,
// no box-shadow, no transitions, no ::pseudo-elements, no box-sizing.
// Tested for: Nokia WAP 2.0 Browser, Opera Mini, NetFront, Openwave.
const XHTML_CSS = `
body{font-family:Arial,Helvetica,sans-serif;margin:0;padding:0;
  background-color:#ecf0f1;color:#1a1a1a;font-size:14px}
.wa-bar{background-color:#075e54;color:#ffffff;padding:10px 12px;
  font-size:15px;font-weight:bold;border-bottom:2px solid #064e46;
  text-align:center}
.wa-bar a{color:#ffffff;text-decoration:none}
.wa-bar small{font-size:11px;font-weight:normal;color:#b2dfdb;display:block;margin-top:2px}
.wa-wrap{max-width:480px;margin:0 auto;padding:6px}
.wml-card{background-color:#ffffff;margin:8px 0;padding:12px 14px;
  border:1px solid #bdc3c7;text-align:center}
.wml-card h2{color:#075e54;font-size:15px;font-weight:bold;margin:0 0 8px 0;
  padding:0 0 8px 0;border-bottom:2px solid #25d366;text-align:center}
a{color:#075e54;text-decoration:none;font-weight:bold}
p{margin:5px 0;padding:0}
b{color:#1a1a1a}
small{font-size:11px;color:#7f8c8d}
hr{border:none;border-top:1px solid #bdc3c7;margin:10px 0}
h1{font-size:15px;color:#ffffff;margin:0;padding:10px 12px;
  background-color:#075e54;border-bottom:2px solid #064e46;text-align:center}
h3{font-size:13px;color:#075e54;margin:8px 0 4px 0;padding:0;text-align:center}
.wml-softkey{display:inline;margin:0 2px}
.wml-softkey a,.wml-softkey button{background-color:#075e54;color:#ffffff;
  padding:6px 14px;text-decoration:none;border:1px solid #064e46;
  font-size:12px;font-weight:bold}
.btn{display:block;background-color:#25d366;color:#ffffff;
  text-align:center;padding:8px 12px;margin:6px auto;
  text-decoration:none;font-weight:bold;font-size:13px;
  border:1px solid #1ebe5b;max-width:280px}
.btn-sm{display:inline;padding:4px 10px;margin:2px 1px;font-size:12px}
.btn-alt{background-color:#075e54;border-color:#064e46}
.btn-danger{background-color:#e74c3c;border-color:#c0392b}
input[type="text"],input[type="password"],textarea{
  width:95%;padding:6px 8px;margin:4px auto;border:1px solid #bdc3c7;
  font-size:13px;font-family:Arial,Helvetica,sans-serif;background-color:#ffffff;
  display:block}
input[type="file"]{margin:4px 0;font-size:12px}
select{padding:6px 8px;margin:4px 0;border:1px solid #bdc3c7;width:95%;
  font-size:13px;font-family:Arial,Helvetica,sans-serif;background-color:#ffffff}
input[type="submit"],button[type="submit"]{background-color:#25d366;color:#ffffff;
  padding:8px 20px;border:1px solid #1ebe5b;font-size:13px;font-weight:bold;
  font-family:Arial,Helvetica,sans-serif;margin:6px 2px}
.inline-form{display:inline}
.msg{padding:6px 10px;margin:4px 0;border-left:3px solid #25d366;
  background-color:#f0faf0;text-align:left}
.msg-out{border-left-color:#34b7f1;background-color:#f0f6fa}
.msg-info{font-size:11px;color:#7f8c8d}
.sep{background-color:#e8f5e9;padding:8px 12px;margin:8px 0;
  border:1px solid #a5d6a7;font-size:12px;color:#2e7d32;text-align:center}
.nav{background-color:#f8f9fa;padding:8px 12px;margin:8px 0;
  border:1px solid #dee2e6;text-align:center}
.nav a{margin:0 6px;font-size:12px}
.upload-section{background-color:#ffffff;margin:8px 0;padding:12px 14px;
  border:1px solid #bdc3c7;text-align:center}
.upload-section h2{color:#075e54;font-size:14px;font-weight:bold;margin:0 0 8px 0;
  padding:0 0 6px 0;border-bottom:2px solid #25d366}
.upload-section label{display:block;font-weight:bold;font-size:11px;color:#555555;
  margin:6px 0 2px 0;text-transform:uppercase}
.upload-section .btn-send{background-color:#25d366;color:#ffffff;padding:8px 16px;
  border:1px solid #1ebe5b;font-size:13px;font-weight:bold;
  font-family:Arial,Helvetica,sans-serif;margin:8px auto;display:block;width:95%;text-align:center}
.cached-section{background-color:#e8f5e9;margin:8px 0;padding:12px 14px;
  border:1px solid #a5d6a7;text-align:center}
.cached-section h2{color:#2e7d32;font-size:13px;font-weight:bold;margin:0 0 6px 0;
  padding:0 0 4px 0;border-bottom:1px solid #a5d6a7}
.back-link{display:block;text-align:center;margin:8px 0;padding:10px;
  background-color:#ffffff;border:1px solid #bdc3c7;color:#075e54;
  font-weight:bold;text-decoration:none}
`;

const HTML5_CSS = `
:root{--wa:#075e54;--wa2:#25d366;--bg:#e5ddd5;--chat:#dcf8c6;--r:10px}
*{box-sizing:border-box;margin:0;padding:0}
body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,Helvetica,Arial,sans-serif;
  background:var(--bg);color:#1a1a1a;font-size:15px;line-height:1.5}
.wml-header{background:var(--wa);color:#fff;padding:14px 16px;font-size:17px;font-weight:600;
  box-shadow:0 2px 6px rgba(0,0,0,.2);text-align:center}
.wml-header a{color:#fff;text-decoration:none}
.wa-wrap{max-width:520px;margin:0 auto;padding:10px}
.wml-card{background:#fff;margin:10px 0;padding:18px 20px;border-radius:var(--r);
  box-shadow:0 1px 4px rgba(0,0,0,.1);text-align:center}
.wml-card h2{color:var(--wa);font-size:17px;font-weight:600;margin:0 0 12px 0;
  padding:0 0 12px 0;border-bottom:2px solid var(--wa2);text-align:center}
a{color:var(--wa);text-decoration:none;font-weight:500}
a:hover{color:var(--wa2);text-decoration:underline}
.wml-softkey{display:inline-block;margin:4px 3px}
.wml-softkey a,.wml-softkey button{background:var(--wa);color:#fff;
  padding:9px 20px;border-radius:24px;text-decoration:none;border:none;
  font-size:13px;font-weight:600;cursor:pointer;font-family:inherit;
  transition:background .15s,transform .1s}
.wml-softkey a:hover,.wml-softkey button:hover{background:var(--wa2);transform:scale(1.03)}
input[type="text"],input[type="password"],textarea{
  width:100%;padding:11px 14px;margin:5px 0;border:2px solid #e0e0e0;border-radius:var(--r);
  font-size:14px;font-family:inherit;transition:border-color .15s;outline:none;
  text-align:center}
input[type="text"]:focus,input[type="password"]:focus,textarea:focus{border-color:var(--wa2);
  box-shadow:0 0 0 3px rgba(37,211,102,.15)}
input[type="file"]{margin:6px 0;font-size:14px}
select{padding:11px 14px;margin:5px 0;border:2px solid #e0e0e0;border-radius:var(--r);
  font-size:14px;font-family:inherit;background:#fff;outline:none;width:100%}
select:focus{border-color:var(--wa2);box-shadow:0 0 0 3px rgba(37,211,102,.15)}
input[type="submit"],button[type="submit"]{background:var(--wa2);color:#fff;
  padding:11px 28px;border:none;border-radius:24px;cursor:pointer;font-size:14px;
  font-weight:600;font-family:inherit;margin:8px 2px;transition:background .15s,transform .1s}
input[type="submit"]:hover,button[type="submit"]:hover{background:var(--wa);transform:scale(1.03)}
p{margin:6px 0}
b{color:#222}
small{color:#7f8c8d;font-size:12px}
.inline-form{display:inline}
hr{border:none;border-top:1px solid #e0e0e0;margin:14px 0}
nav{background:var(--wa);padding:12px 16px;position:sticky;top:0;z-index:10;
  box-shadow:0 2px 4px rgba(0,0,0,.15);text-align:center}
nav a{color:#fff;margin:0 8px;text-decoration:none;font-weight:500;font-size:14px}
nav a:hover{text-decoration:underline;color:#b2dfdb}
.msg{padding:8px 12px;margin:5px 0;border-left:3px solid var(--wa2);
  background-color:#f0faf0;border-radius:0 var(--r) var(--r) 0;text-align:left}
.msg-out{border-left-color:#34b7f1;background-color:#f0f6fa}
.msg-info{font-size:11px;color:#7f8c8d}
.sep{background-color:#e8f5e9;padding:8px 14px;margin:8px 0;border-radius:var(--r);
  border:1px solid #a5d6a7;font-size:12px;color:#2e7d32;text-align:center}
.nav-wrap{background-color:#f8f9fa;padding:10px 14px;margin:8px 0;border-radius:var(--r);
  border:1px solid #dee2e6;text-align:center}
.nav-wrap a{margin:0 6px;font-size:13px}
.upload-section{background:#fff;margin:10px 0;padding:20px;border-radius:var(--r);
  box-shadow:0 1px 4px rgba(0,0,0,.1);text-align:center}
.upload-section h2{color:var(--wa);font-size:16px;font-weight:600;margin:0 0 14px 0;
  padding:0 0 12px 0;border-bottom:2px solid #f0f0f0;text-align:center}
.upload-section label{display:block;font-weight:600;font-size:12px;color:#666;
  margin:10px 0 4px 0;text-transform:uppercase;letter-spacing:.5px}
.upload-section .btn-send{background:var(--wa2);color:#fff;padding:12px 24px;border:none;
  border-radius:var(--r);cursor:pointer;font-size:15px;font-weight:600;font-family:inherit;
  margin:14px auto;display:block;width:100%;max-width:320px;text-align:center;transition:background .15s}
.upload-section .btn-send:hover{background:var(--wa)}
.cached-section{background:#e8f5e9;margin:10px 0;padding:18px 20px;border-radius:var(--r);
  border:2px solid #a5d6a7;text-align:center}
.cached-section h2{color:#2e7d32;font-size:15px;font-weight:600;margin:0 0 8px 0;
  padding:0 0 8px 0;border-bottom:1px solid #a5d6a7}
.back-link{display:block;text-align:center;margin:12px 0;padding:13px;border-radius:var(--r);
  background:#fff;box-shadow:0 1px 3px rgba(0,0,0,.1);color:var(--wa);font-weight:600;
  text-decoration:none;transition:background .15s}
.back-link:hover{background:#e8f5e9}
`;

function transformWmlToMarkup(wmlStr, mode) {
  if (mode === 'wml') return wmlStr;

  // Helper: extract postfields from inner <go> content, return {hiddens, hasVarRefs}
  function extractPostfields(inner) {
    let hiddens = '';
    let hasVarRefs = false;
    const pfRegex = /<postfield\s+name="([^"]*?)"\s+value="([^"]*?)"\s*\/?>/g;
    let pfMatch;
    while ((pfMatch = pfRegex.exec(inner)) !== null) {
      const pfName = pfMatch[1];
      const pfValue = pfMatch[2];
      if (/^\$\([^)]+\)$/.test(pfValue)) {
        hasVarRefs = true;
      } else {
        hiddens += `<input type="hidden" name="${esc(pfName)}" value="${esc(pfValue)}"/>`;
      }
    }
    return { hiddens, hasVarRefs };
  }

  // Helper: extract href and method from a <go> tag regardless of attribute order
  function parseGoAttrs(goTag) {
    const hrefMatch = goTag.match(/href="([^"]*?)"/);
    const methodMatch = goTag.match(/method="([^"]*?)"/);
    return {
      href: hrefMatch ? hrefMatch[1].replace(/&amp;/g, '&') : '',
      method: methodMatch ? methodMatch[1] : 'get'
    };
  }

  let content = wmlStr;
  let timerUrl = null;
  let timerValue = null; // in 1/10s of a second

  // --- 1. Extract timer info ---
  const ontimerMatch = content.match(/ontimer="([^"]+)"/);
  if (ontimerMatch) timerUrl = ontimerMatch[1].replace(/&amp;/g, '&');
  const oneventTimerMatch = content.match(/<onevent\s+type="ontimer">\s*<go\s+href="([^"]+)"[^>]*\/>\s*<\/onevent>/s);
  if (oneventTimerMatch) timerUrl = oneventTimerMatch[1].replace(/&amp;/g, '&');
  const timerMatch = content.match(/<timer\s+value="(\d+)"[^>]*\/?>/);
  if (timerMatch) timerValue = parseInt(timerMatch[1], 10);

  // --- 2. Remove WML-specific event/timer/variable elements ---
  content = content.replace(/<onevent[^>]*>[\s\S]*?<\/onevent>/g, '');
  content = content.replace(/<timer\s[^>]*\/?>/g, '');
  content = content.replace(/<setvar\s[^>]*\/?>/g, '');
  content = content.replace(/<refresh>[\s\S]*?<\/refresh>/g, '');
  content = content.replace(/<noop\s*\/?>/g, '');
  content = content.replace(/<prev\s*\/?>/g, '');

  // --- 3. Transform <do> elements (handles any attribute order on <go>) ---
  // Match <do type="X" label="Y">...<go ...>...</go></do>
  content = content.replace(
    /<do\s+type="([^"]*?)"\s+label="([^"]*?)">\s*(<go\s[^>]*>)([\s\S]*?)<\/go>\s*<\/do>/gs,
    (_, type, label, goTag, goInner) => {
      const { href, method } = parseGoAttrs(goTag);
      if (method === 'post') {
        const { hiddens } = extractPostfields(goInner);
        return `<div class="wml-softkey wml-softkey-${esc(type)}"><form method="post" action="${esc(href)}" class="inline-form">${hiddens}<button type="submit">${esc(label)}</button></form></div>`;
      }
      return `<div class="wml-softkey wml-softkey-${esc(type)}"><a href="${esc(href)}">${esc(label)}</a></div>`;
    }
  );
  // Also handle <do> with self-closing <go href="..."/>
  content = content.replace(
    /<do\s+type="([^"]*?)"\s+label="([^"]*?)">\s*<go\s+href="([^"]*?)"[^>]*\/>\s*<\/do>/gs,
    (_, type, label, href) => {
      const decodedHref = href.replace(/&amp;/g, '&');
      return `<div class="wml-softkey wml-softkey-${esc(type)}"><a href="${esc(decodedHref)}">${esc(label)}</a></div>`;
    }
  );

  // --- 4. Transform <anchor> with <go> + postfields (any attribute order) ---
  content = content.replace(
    /<anchor[^>]*>([\s\S]*?)(<go\s[^>]*>)([\s\S]*?)<\/go>\s*<\/anchor>/gs,
    (_, labelContent, goTag, goInner) => {
      const { href, method } = parseGoAttrs(goTag);
      const label = labelContent.replace(/<[^>]+>/g, '').trim();
      if (method === 'post') {
        const { hiddens } = extractPostfields(goInner);
        return `<form method="post" action="${esc(href)}" class="inline-form">${hiddens}<button type="submit">${esc(label)}</button></form>`;
      }
      return `<a href="${esc(href)}">${esc(label)}</a>`;
    }
  );
  // Also handle <anchor> with self-closing <go href="..."/>
  content = content.replace(
    /<anchor[^>]*>([\s\S]*?)<go\s+href="([^"]*?)"[^>]*\/>\s*<\/anchor>/gs,
    (_, labelContent, href) => {
      const label = labelContent.replace(/<[^>]+>/g, '').trim();
      return `<a href="${href}">${esc(label)}</a>`;
    }
  );

  // --- 5. Handle $(varname) references: rename mismatched input names ---
  const varRenames = {};
  const pfScan = /<postfield\s+name="([^"]*?)"\s+value="\$\(([^)]+)\)"\s*\/?>/g;
  let scanMatch;
  const tempContent = wmlStr;
  while ((scanMatch = pfScan.exec(tempContent)) !== null) {
    const postName = scanMatch[1];
    const varName = scanMatch[2];
    if (postName !== varName) {
      varRenames[varName] = postName;
    }
  }
  for (const [oldName, newName] of Object.entries(varRenames)) {
    content = content.replace(
      new RegExp(`(<input[^>]*?)\\sname="${oldName}"`, 'g'),
      `$1 name="${newName}"`
    );
  }

  // --- 6. Map <input title="X"> → <input placeholder="X"> ---
  content = content.replace(
    /(<input[^>]*?)\stitle="([^"]*?)"([^>]*?>)/g,
    '$1 placeholder="$2"$3'
  );

  // --- 7. Map <select title="X"> → <label>X</label><select> ---
  content = content.replace(
    /<select([^>]*?)\stitle="([^"]*?)"([^>]*?)>/g,
    '<label>$2</label><select$1$3>'
  );

  // --- 8. Strip WML-specific attributes not valid in HTML ---
  content = content.replace(/\s(?:emptyok|format|iname|ivalue|localsrc|sendreferer|ordered)="[^"]*?"/g, '');

  // --- 9. Fix password fields: name="password" type="text" → type="password" ---
  content = content.replace(
    /(<input[^>]*?name="password"[^>]*?)type="text"/g,
    '$1type="password"'
  );
  // Also handle reversed order: type="text" ... name="password"
  content = content.replace(
    /(<input[^>]*?)type="text"([^>]*?name="password")/g,
    '$1type="password"$2'
  );

  // --- 10. Transform <card> → <div> ---
  let pageTitle = 'WhatsApp WAP';
  const firstCardTitle = content.match(/<card\s[^>]*?title="([^"]*?)"/);
  if (firstCardTitle) pageTitle = firstCardTitle[1];

  content = content.replace(
    /<card\s+id="([^"]*?)"\s+title="([^"]*?)"[^>]*>/gs,
    (_, id, title) => `<div class="wml-card" id="${esc(id)}"><h2>${esc(title)}</h2>`
  );
  content = content.replace(/<\/card>/g, '</div>');

  // --- 11. Strip WMLScript references ---
  content = content.replace(/<script\s[^>]*type="text\/vnd\.wap\.wmlscriptc"[^>]*\/>/g, '');
  content = content.replace(/<script\s[^>]*src="\/wmlscript\/[^"]*"[^>]*\/>/g, '');

  // --- 12. Strip WML document envelope ---
  content = content.replace(/<\?xml[^?]*\?>\s*/g, '');
  content = content.replace(/<!DOCTYPE[^>]*>\s*/g, '');
  content = content.replace(/<wml>\s*/g, '');
  content = content.replace(/\s*<\/wml>/g, '');
  content = content.replace(/<head>[\s\S]*?<\/head>\s*/g, '');

  // --- 13. Clean up remaining WML artifacts ---
  // Strip any leftover <postfield> tags
  content = content.replace(/<postfield\s[^>]*\/?>/g, '');
  // Self-close void elements for XHTML-MP validity
  if (mode === 'xhtml') {
    content = content.replace(/<(br|hr|img|input|meta|link)(\s[^>]*)?\s*(?<!\/)>/g, '<$1$2/>');
  }

  // Build timer markup
  let timerHtml = '';
  if (timerUrl && timerValue) {
    const seconds = Math.max(1, Math.round(timerValue / 10));
    if (mode === 'xhtml') {
      timerHtml = `<meta http-equiv="refresh" content="${seconds};url=${esc(timerUrl)}"/>`;
    } else {
      timerHtml = `<script>setTimeout(function(){window.location.href='${timerUrl.replace(/'/g, "\\'")}'},${seconds * 1000})</script>`;
    }
  }

  // --- 12. Clean up excess whitespace ---
  content = content.replace(/\n{3,}/g, '\n\n');
  content = content.replace(/^\s+$/gm, '');

  // Build final XHTML Mobile Profile 1.0 document
  if (mode === 'xhtml') {
    return `<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE html PUBLIC "-//WAPFORUM//DTD XHTML Mobile 1.0//EN" "http://www.wapforum.org/DTD/xhtml-mobile10.dtd">
<html xmlns="http://www.w3.org/1999/xhtml" xml:lang="en">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=utf-8"/>
<meta http-equiv="Cache-Control" content="no-cache, no-store"/>
<title>${esc(pageTitle)} - WhatsApp</title>
<style type="text/css">${XHTML_CSS}</style>
${timerHtml}
</head>
<body>
<div class="wa-bar"><a href="/wml/home.wml">WhatsApp</a> <small>${esc(pageTitle)}</small></div>
<div class="wa-wrap">
${content}
</div>
</body>
</html>`;
  }

  // HTML5
  return `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8"/>
<meta name="viewport" content="width=device-width,initial-scale=1"/>
<meta http-equiv="Cache-Control" content="no-cache, no-store"/>
<title>${esc(pageTitle)} - WhatsApp</title>
<style>${HTML5_CSS}</style>
${timerHtml}
</head>
<body>
<div class="wml-header"><a href="/wml/home.wml">WhatsApp</a> - ${esc(pageTitle)}</div>
<div class="wa-wrap">
${content}
</div>
</body>
</html>`;
}

function wmlDoc(cards, scripts = "") {
  const head = scripts
    ? `<head><meta http-equiv="Cache-Control" content="no-cache, no-store"/>${scripts}</head>`
    : '<head><meta http-equiv="Cache-Control" content="no-cache, no-store"/></head>';
  return `<?xml version="1.0" encoding="ISO-8859-1"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.0//EN" "http://www.wapforum.org/DTD/wml_1.0.xml">
<wml>${head}${cards}</wml>`;
}


// Append ?auth=TOKEN to a WML URL so WAP 1.x devices stay authenticated.
// Simple redirect helper (no token injection needed — auth is cookie-based)
function authRedirect(res, url, code = 302) {
  return res.redirect(code, url);
}

function sendWml(res, cards, scripts = "", modeOverride = null) {
  const mode = modeOverride || MARKUP_MODE;
  res.setHeader("Cache-Control", "no-cache, no-store, must-revalidate");
  res.setHeader("Pragma", "no-cache");
  res.setHeader("Expires", "0");
  res.setHeader("Accept-Ranges", "none");

  const wmlContent = wmlDoc(cards, scripts);

  if (mode === 'wml') {
    const encodedBuffer = iconv.encode(wmlContent, 'iso-8859-1');
    res.setHeader("Content-Type", "text/vnd.wap.wml; charset=iso-8859-1");
    res.send(encodedBuffer);
  } else {
    const transformed = transformWmlToMarkup(wmlContent, mode);
    // Serve XHTML as text/html for maximum browser compatibility.
    // application/vnd.wap.xhtml+xml causes many browsers to treat the response
    // as an unknown file type instead of rendering it.
    res.setHeader("Content-Type", "text/html; charset=utf-8");
    res.send(transformed);
  }
}

// Sends raw WML content with MARKUP_MODE awareness.
// Use this instead of manually setting Content-Type text/vnd.wap.wml and sending.
function sendRawWmlAware(res, wmlStr) {
  res.setHeader("Cache-Control", "no-cache, no-store, must-revalidate");
  res.setHeader("Pragma", "no-cache");
  res.setHeader("Expires", "0");

  if (MARKUP_MODE === 'wml') {
    res.setHeader("Content-Type", "text/vnd.wap.wml; charset=iso-8859-1");
    res.send(iconv.encode(wmlStr, 'iso-8859-1'));
  } else {
    const transformed = transformWmlToMarkup(wmlStr, MARKUP_MODE);
    // Serve XHTML as text/html for maximum browser compatibility.
    res.setHeader("Content-Type", "text/html; charset=utf-8");
    res.send(transformed);
  }
}

function card(id, title, inner, ontimer = null, scripts = '') {
  const timerUnits = getWmlRefreshTimerUnits();
  const timerVarName = "rtv";
  const timerNonce = Date.now();
  const timerVarRef = `$(${timerVarName})`;
  const timerTarget = ontimer
    ? `${ontimer}${ontimer.includes("?") ? "&" : "?"}_rt=${timerNonce}&_rv=${timerVarRef}`
    : null;
  const timerAttr = timerTarget ? ` ontimer="${esc(timerTarget)}"` : "";
  const timerEl = ontimer ? `<timer value="${timerUnits}"/>` : "";
  const timerEvent = timerTarget
    ? `<onevent type="ontimer"><go href="${esc(timerTarget)}"/></onevent>`
    : "";
  const timerVarInit = ontimer
    ? `<onevent type="onenterforward"><refresh><setvar name="${timerVarName}" value="${timerNonce}"/></refresh></onevent>`
    : "";
  return `<card id="${esc(id)}" title="${esc(title)}"${timerAttr}>
    ${timerVarInit}
    ${timerEvent}
    ${timerEl}
    ${scripts}
    ${inner}
  </card>`;
}

function truncate(s = "", max = 64) {
  const str = String(s);
  return str.length > max ? str.slice(0, max - 3) + "..." : str;
}



async function getContactName(jid, sock) {
  if (!jid) return "Unknown";

  const isGroup = jid.endsWith("@g.us");
  const isLid = jid.startsWith('lid:'); // Check LID early

  // Try to get from contactStore first (cached)
  let contact = contactStore.get(jid);

  // If not found and it's not a group and NOT a LID, try alternative lookups
  if (!contact && !isGroup && !isLid) {
    // Try with formatted JID
    const formattedJid = formatJid(jid);
    if (formattedJid !== jid) {
      contact = contactStore.get(formattedJid);
    }

    // If still not found, try by phone number via O(1) index
    if (!contact) {
      const phoneNumber = jidFriendly(jid);
      const contactKey = phoneToContactIndex.get(phoneNumber);
      if (contactKey) {
        contact = contactStore.get(contactKey);
      }
    }
  }

  if (isGroup) {
    // For groups, try multiple sources
    if (contact?.subject) return contact.subject;
    if (contact?.name) return contact.name;

    // Try to fetch group metadata if sock is available
    if (sock) {
      try {
        const groupMetadata = await sock.groupMetadata(jid);
        if (groupMetadata?.subject) {
          // Cache it
          contactStore.set(jid, { ...contact, subject: groupMetadata.subject });
          return groupMetadata.subject;
        }
      } catch (error) {
        // Silently fail, use fallback
      }
    }

    // Fallback for groups
    const groupId = jid.replace("@g.us", "");
    return `Group ${groupId.slice(-8)}`;
  } else if (isLid) {
    // Handle LID contacts - DO NOT call onWhatsApp
    if (contact?.phoneNumber) {
      return contact.phoneNumber; // Show phone number if available
    }
    if (contact?.name) return contact.name;
    if (contact?.notify) return contact.notify;
    if (contact?.verifiedName) return contact.verifiedName;

    // Fallback: show truncated LID
    return `LID:${jid.substring(4, 12)}...`;
  } else {
    // For individual contacts (phone number based)
    if (contact?.phoneNumber) {
      return contact.phoneNumber; // Show phone number if available
    }
    if (contact?.name) return contact.name;
    if (contact?.notify) return contact.notify;
    if (contact?.verifiedName) return contact.verifiedName;

    // Try to get from WhatsApp ONLY for phone numbers (NOT LIDs)
    if (sock) {
      try {
        const queryJid = formatJid(jid);
        const [result] = await sock.onWhatsApp(queryJid);
        if (result?.exists) {
          const name = result.name || result.notify;
          if (name) {
            // Cache it with new structure
            const phoneNum = jidFriendly(jid);
            contactStore.set(jid, {
              id: queryJid,
              name: name,
              phoneNumber: phoneNum
            });
            // Maintain phone→contact index
            if (phoneNum) phoneToContactIndex.set(phoneNum, jid);
            return name;
          }
        }
      } catch (error) {
        // Silently fail, use fallback
      }
    }

    // Fallback to formatted phone number
    return jidFriendly(jid);
  }
}

function parseList(str = "") {
  return String(str)
    .split(/[,;\s]+/)
    .map((s) => s.trim())
    .filter(Boolean);
}

// Update formatJid function to handle LIDs
// Update formatJid function to handle LIDs
function formatJid(raw = "") {
  const s = String(raw).trim();
  if (!s) return s;

  // If it's already a LID (contains colon), return as-is
  if (s.includes(':')) {
    return s;
  }

  // For phone numbers, add domain
  return s.includes("@") ? s : `${s}@s.whatsapp.net`;
}


function jidFriendly(jid = "") {
  if (!jid) return "";
  
  // Handle LIDs
  if (jid.startsWith('lid:')) {
    return `LID:${jid.substring(4)}`;
  }
  
  if (jid.endsWith("@s.whatsapp.net"))
    return jid.replace("@s.whatsapp.net", "");
  if (jid.endsWith("@g.us")) return `Group ${jid.slice(0, -5)}`;
  return jid;
}

function ensureGroupJid(raw = "") {
  const s = String(raw).trim();
  if (!s) return s;
  return s.endsWith("@g.us") ? s : `${s}@g.us`;
}

function messageText(msg) {
  try {
    if (!msg) return "[No message]";

    const c = extractMessageContent(msg?.message);
    if (!c) return "[Unsupported message]";
    const inlineText = extractInlineTextFromContent(c);

    if (c.stickerMessage) return stickerTextWithOptionalText(c.stickerMessage, inlineText, true);

    if (c.conversation) return c.conversation || "[Empty message]";
    if (c.extendedTextMessage?.text)
      return c.extendedTextMessage.text || "[Empty text]";
    if (c.imageMessage?.caption) return `[IMG] ${c.imageMessage.caption || ""}`;
    if (c.videoMessage?.caption) return `[VID] ${c.videoMessage.caption || ""}`;
    if (c.audioMessage) {
      const duration = c.audioMessage.seconds || 0;
      const transcription = msg.transcription || "";

      let result = `[AUDIO ${duration}s]`;

      // Add transcription indicator if available
      if (
        transcription &&
        transcription !== "[Trascrizione fallita]" &&
        transcription !== "[Audio troppo lungo per la trascrizione]"
      ) {
        result += " [TXT]";
      }

      return result;
    }
    if (c.documentMessage)
      return `[DOC] ${c.documentMessage.fileName || "Document"}`;

    const type = getContentType(msg?.message) || "unknown";
    return `[${type.toUpperCase()}]`;
  } catch (error) {
    console.error("Error in messageText:", error);
    return "[Error]";
  }
}
function resultCard(
  title,
  lines = [],
  backHref = "/wml/home.wml",
  autoRefresh = true
) {
  const onTimer = autoRefresh ? ` ontimer="${esc(backHref)}"` : "";

  const body = `
    <p><b>${esc(title)}</b></p>
    ${lines.map((l) => `<p>${esc(l)}</p>`).join("")}
    <p>
      <a href="${esc(backHref)}" accesskey="0">${t('common.back')}</a>
      <a href="/wml/home.wml" accesskey="9">${t('home.title')}</a>
    </p>
    <do type="accept" label="${t('common.ok')}">
      <go href="${esc(backHref)}"/>
    </do>
    <do type="options" label="${t('common.menu')}">
      <go href="/wml/home.wml"/>
    </do>
  `;
  return `<card id="result" title="${esc(title)}"${onTimer}>${body}</card>`;
}

function navigationBar() {
  return `
    <p>
      <a href="/wml/home.wml" accesskey="1">${t('home.title')}</a>
      <a href="/wml/chats.wml" accesskey="2">${t('home.chats')}</a>
      <a href="/wml/contacts.wml" accesskey="3">${t('home.contacts')}</a>
      <a href="/wml/send-menu.wml" accesskey="4">${t('common.send')}</a>
    </p>
  `;
}

function searchBox(action, placeholder = null) {
  const safeAction = esc(action);
  const ph = placeholder || t('common.search') + '...';
  return `
    <p>
      <input name="q" title="${esc(ph)}" size="20" maxlength="50"/>
    </p>
    <p>
      <anchor title="${t('common.search')}">${t('common.search')}
        <go href="${safeAction}" method="get">
          <postfield name="q" value="$(q)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.search')}">
      <go href="${safeAction}" method="get">
        <postfield name="q" value="$(q)"/>
      </go>
    </do>
  `;
}

// WMLScript functions
function wmlScript(name, functions) {
  return `<script src="/wmlscript/${name}.wmls?_rt=${Date.now()}" type="text/vnd.wap.wmlscriptc"/>`;
}

// ============ LOGIN / LOGOUT ROUTES (WML) ============
app.get("/login", (req, res) => {
  sendWml(res, card('login', t('login.title'), `
    <p><b>${t('app_name')}</b></p>
    <p>${t('login.user')}
      <input name="usr" type="text" maxlength="64"/>
    </p>
    <p>${t('login.password')}
      <input name="pw" type="text" maxlength="64"/>
    </p>
    <p>
      <anchor title="${t('login.submit')}">${t('login.submit')}
        <go href="/login" method="post">
          <postfield name="user" value="$(usr)"/>
          <postfield name="password" value="$(pw)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('login.submit')}">
      <go href="/login" method="post">
        <postfield name="user" value="$(usr)"/>
        <postfield name="password" value="$(pw)"/>
      </go>
    </do>
  `));
});

app.get("/login-error", (req, res) => {
  sendWml(res, card('login-error', t('login_error.title'), `
    <p><b>${t('login_error.wrong_password')}</b></p>
    <p>${t('login_error.invalid_credentials')}</p>
    <p>
      <anchor title="${t('login.submit')}">${t('login_error.back')}
        <go href="/login"/>
      </anchor>
    </p>
    <do type="accept" label="${t('login.submit')}">
      <go href="/login"/>
    </do>
  `));
});

app.get("/login-success", (req, res) => {
  sendWml(res, card('login-ok', t('login_success.title'), `
    <p align="center"><b>${t('login_success.message')}</b></p>
    <p align="center">
      <anchor title="${t('home.title')}">${t('login_success.go_home')}
        <go href="/wml/home.wml"/>
      </anchor>
    </p>
  `));
});

app.post("/login", (req, res) => {
  const { user, password } = req.body;
  const storedUser = authDb.prepare('SELECT value FROM config WHERE key = ?').get('username');
  if (!storedUser || user !== storedUser.value) {
    console.log('[AUTH] Login failed for user:', user);
    return sendWml(res, card('login-fail', t('login_error.title'), `
      <p><b>${t('login_error.wrong_password')}</b></p>
      <p>${t('login_error.invalid_credentials')}</p>
      <p>
        <anchor title="${t('login.submit')}">${t('login_error.back')}
          <go href="/login"/>
        </anchor>
      </p>
      <do type="accept" label="${t('login.submit')}">
        <go href="/login"/>
      </do>
    `));
  }
  const row = authDb.prepare('SELECT value FROM config WHERE key = ?').get('password_hash');
  if (row && bcrypt.compareSync(password || '', row.value)) {
    req.session.authenticated = true;
    req.session.authUser = user;
    return req.session.save((err) => {
      if (err) {
        console.error('[AUTH] Session save error:', err);
        return sendWml(res, card('login-fail', t('login_error.title'), `
          <p><b>${t('login_error.session_error')}</b></p>
          <p>${t('login_error.session_persist')}</p>
          <p>
            <anchor title="${t('login.submit')}">${t('login_error.back')}
              <go href="/login"/>
            </anchor>
          </p>
          <do type="accept" label="${t('login.submit')}">
            <go href="/login"/>
          </do>
        `));
      }
      console.log('[AUTH] Login successful for user:', user, '| Session ID:', req.sessionID);
      // Don't use HTTP redirect — WAP 1.x gateways may drop Set-Cookie on 302.
      // Serve a success page directly so the cookie travels with the rendered response.
      return sendWml(res, card('login-ok', t('login.title'), `
        <p><b>${t('app_name')}</b></p>
        <p>${t('login_success.message')}</p>
        <p>
          <a href="/wml/home.wml">${t('qr.go_home')}</a>
        </p>
        <do type="accept" label="${t('qr.go_home')}">
          <go href="/wml/home.wml"/>
        </do>
      `, "/wml/home.wml"));
    });
  }
  console.log('[AUTH] Login failed for user:', user);
  sendWml(res, card('login-fail', t('login_error.title'), `
    <p><b>${t('login_error.wrong_password')}</b></p>
    <p>${t('login_error.invalid_credentials')}</p>
    <p>
      <anchor title="${t('login.submit')}">${t('login_error.back')}
        <go href="/login"/>
      </anchor>
    </p>
    <do type="accept" label="${t('login.submit')}">
      <go href="/login"/>
    </do>
  `));
});

app.get("/logout", (req, res) => {
  req.session.destroy(() => {
    sendWml(res, card('logout', t('logout.title'), `
      <p align="center"><b>${t('logout.message')}</b></p>
      <p>
        <anchor title="${t('login.submit')}">${t('logout.go_login')}
          <go href="/login"/>
        </anchor>
      </p>
      <do type="accept" label="${t('login.submit')}">
        <go href="/login"/>
      </do>
    `));
  });
});

// WMLScript files endpoint
app.get("/wmlscript/:filename", (req, res) => {
  if (MARKUP_MODE !== 'wml') {
    return res.status(404).send('WMLScript not available in current markup mode');
  }
  const { filename } = req.params;
  let script = "";

  res.setHeader("Content-Type", "text/vnd.wap.wmlscript");
  res.setHeader("Cache-Control", "no-cache, no-store, must-revalidate");
  res.setHeader("Pragma", "no-cache");
  res.setHeader("Expires", "0");

  switch (filename) {
    case "utils.wmls":
      script = `
extern function refresh();
extern function confirmAction(message);
extern function showAlert(text);

function refresh() {
  WMLBrowser.refresh();
}

function confirmAction(message) {
  var result = Dialogs.confirm(message, "Confirm", "Yes", "No");
  return result;
}

function showAlert(text) {
  Dialogs.alert(text);
}
`;
      break;
    case "wtai.wmls":
      script = `
extern function makeCall(number);
extern function sendSMS(number, message);
extern function addContact(name, number);

function makeCall(number) {
  WTAVoice.setup("wtai://wp/mc;" + number, "");
}

function sendSMS(number, message) {
  WTASMS.send("wtai://wp/ms;" + number + ";" + message, "");
}

function addContact(name, number) {
  WTAPhoneBook.write("wtai://wp/ap;" + name + ";" + number, "");
}
`;
      break;
    default:
      return res.status(404).send("Script not found");
  }

  res.send(script);
});

// Enhanced Home page with WMLScript integration
app.get(["/wml", "/wml/home.wml", "/wml/home.eml", "/home.wml", "/home.eml"], (req, res) => {
  const connected = !!sock?.authState?.creds && connectionState === 'open';
  const refreshNonce = Date.now();

  // Redirect to QR only if WhatsApp has NEVER been authenticated (no credentials at all).
  // If credentials exist but connection is temporarily down (reconnecting), show cached home
  // so users always see their chats and are never stuck in a QR redirect loop.
  if (!sock?.authState?.creds) {
    return authRedirect(res, '/wml/qr.wml');
  }

  const unreadCount = getUnreadCount();
  const recentChats = getRecentChats(3);

  // Favorites section - show up to 3 with numbered shortcuts
  let favoritesHtml = '';
  if (userSettings.favorites.length > 0) {
    favoritesHtml = `<p><b>${t('home.favorites_header')}</b></p><p>`;
    for (let i = 0; i < Math.min(3, userSettings.favorites.length); i++) {
      const jid = userSettings.favorites[i];
      const contact = contactStore.get(jid);
      const name = contact?.name || contact?.notify || jidFriendly(jid);
      favoritesHtml += `<a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}">[${i + 1}] ${esc(name.substring(0, 12))}</a><br/>`;
    }
    if (userSettings.favorites.length > 3) {
      favoritesHtml += `<a href="/wml/favorites.wml">[+${userSettings.favorites.length - 3} ${t('common.more')}]</a>`;
    }
    favoritesHtml += '</p>';
  }

  const recentHtml = buildRecentChatsHtml(recentChats, false);

  const statusStr = connected ? t('home.status_on') : t('home.status_off');
  const syncStr = isFullySynced ? t('home.status_ok') : t('home.status_syncing');

  const body = `
    <p><b>${t('app_name')}</b></p>
    <p>${statusStr}${syncStr}</p>

    ${recentHtml}
    <p> </p>
    ${favoritesHtml}

    <p><b>${t('home.menu_header')}</b></p>
    <p>
      <a href="/wml/chats.wml" accesskey="1">${t('home.chats')}</a><br/>
      <a href="/wml/contacts.wml" accesskey="2">${t('home.contacts')}</a><br/>
      <a href="/wml/send-menu.wml" accesskey="3">${t('home.new_message')}</a><br/>
      <a href="/wml/groups.wml" accesskey="4">${t('home.groups')}</a><br/>
      <a href="/wml/favorites.wml" accesskey="5">${t('home.favorites')}</a><br/>
      <a href="/wml/status-broadcast.wml" accesskey="6">${t('home.post_status')}</a>
    </p>

    <p><b>${t('home.tools_header')}</b></p>
    <p>
      <a href="/wml/search.wml" accesskey="7">${t('home.search')}</a><br/>
      <a href="/wml/settings.wml" accesskey="8">${t('home.settings')}</a><br/>
      <a href="/wml/help.wml" accesskey="9">${t('home.help')}</a><br/>
      <a href="/wml/me.wml">${t('home.profile')}</a><br/>
      <a href="/wml/qr.wml">${t('home.qr_code')}</a><br/>
      <a href="/wml/status.wml">${t('home.sys_status')}</a><br/>
      <a href="/wml/logout.wml" accesskey="0">${t('home.logout')}</a>
    </p>

    <do type="accept" label="${t('chats.title')}">
      <go href="/wml/chats.wml"/>
    </do>
    <do type="options" label="${t('common.refresh')}">
      <go href="/wml/home.wml?_rt=${refreshNonce}"/>
    </do>
    <do type="options" label="${t('settings.title')}">
      <go href="/wml/settings.wml"/>
    </do>
  `;

  sendWml(res, card("home", t('home.title'), body, "/wml/home.wml"));
});

/*
  const limit = 3 // Messaggi per pagina
  const offset = Math.max(0, parseInt(req.query.offset || '0'))
  const search = (req.query.search || '').trim().toLowerCase()

  // Chat history is loaded from persistent storage on startup
  // No need to fetch from WhatsApp servers every time
  // The initial sync already handles this

  // Messages already stored oldest→newest via binary insertion — no sort needed
  let allMessages = (chatStore.get(jid) || []).slice()

  // Applica filtro di ricerca se presente
  if (search) {
    allMessages = allMessages.filter(m => (messageText(m) || '').toLowerCase().includes(search))
  }

  // Per la paginazione con ordinamento crescente, prendiamo gli ultimi messaggi
  // ma li mostriamo nell'ordine corretto (dal più vecchio al più recente)
  const totalMessages = allMessages.length
  const startIndex = Math.max(0, totalMessages - limit - offset)
  const endIndex = totalMessages - offset
  const slice = allMessages.slice(startIndex, endIndex)

  const contact = contactStore.get(jid)
  const chatName = contact?.name || contact?.notify || contact?.verifiedName || jidFriendly(jid)
  const number = jidFriendly(jid)

  // Escape sicuro e rimuove caratteri non ASCII
  // Uses global escWml — single-pass O(L) instead of O(5L)

  let messageList
  if (slice.length === 0) {
    messageList = `<p>${t('chat.no_messages')}</p>
      <p>
        <a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}" accesskey="2">${t('chat.clear_search')}</a> |
        <a href="/wml/chats.wml" accesskey="0">${t('chat.back_to_chats')}</a>
      </p>`
  } else {
    messageList = slice.map((m, idx) => {
      const who = m.key.fromMe ? t('chat.me') : chatName
      const text = truncate(messageText(m), 100)
      const tsDate = new Date(Number(m.messageTimestamp) * 1000)
      const ts = tsDate.toLocaleDateString('en-GB', { day: '2-digit', month: '2-digit', year: 'numeric' }) + ' ' + tsDate.toLocaleTimeString('en-GB', { hour: '2-digit', minute: '2-digit', second: '2-digit' })
      const mid = m.key.id
      
      return `<p><b>${idx + 1}. ${escWml(who)}</b> (${ts})<br/>
        ${escWml(text)}<br/>
        <a href="/wml/msg.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}" accesskey="${Math.min(idx + 1, 9)}">[Actions]</a>
      </p>`
    }).join('')
  }

  // Navigazione corretta per ordinamento crescente
  const olderOffset = offset + limit
  const olderLink = olderOffset < totalMessages
    ? `<a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}&amp;offset=${olderOffset}&amp;search=${encodeURIComponent(search)}" accesskey="2">${t('chat.older')}</a>` : ''

  const newerOffset = Math.max(0, offset - limit)
  const newerLink = offset > 0
    ? `<a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}&amp;offset=${newerOffset}&amp;search=${encodeURIComponent(search)}" accesskey="3">${t('chat.newer')}</a>` : ''

  // Search form sempre visibile
  const searchForm = `
    <p><b>${t('chat.search_messages')}</b></p>
    <p>
      <input name="searchQuery" title="${t('chat.search_placeholder')}" value="${escWml(search)}" size="15" maxlength="50"/>
    </p>
    <p>
      <anchor title="${t('common.search')}">${t('common.search')}
        <go href="/wml/chat.wml" method="get">
          <postfield name="jid" value="${escWml(jid)}"/>
          <postfield name="search" value="$(searchQuery)"/>
          <postfield name="offset" value="0"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.search')}">
      <go href="/wml/chat.wml" method="get">
        <postfield name="jid" value="${escWml(jid)}"/>
        <postfield name="search" value="$(searchQuery)"/>
        <postfield name="offset" value="0"/>
      </go>
    </do>
    ${search ? `<p>${t('chat.searching')} <b>${escWml(search)}</b> | <a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}">${t('chat.clear_search')}</a></p>` : ''}
  `

  // Indicatori di paginazione migliorati
  const currentPage = Math.floor(offset / limit) + 1
  const totalPages = Math.ceil(totalMessages / limit)
  const paginationInfo = `
    <p><b>${t('chat.total')} ${totalMessages} ${t('chat.messages')}</b></p>
    <p>${t('chat.page')} ${currentPage}/${totalPages}</p>
  `

  const body = `
    <p><b>${escWml(chatName)}</b></p>
    <p>${escWml(number)} | ${t('chat.total')} ${totalMessages} ${t('chat.messages')}</p>

    ${searchForm}

    ${paginationInfo}

    ${messageList}

    <p><b>${t('chat.navigation')}</b></p>
    <p>${olderLink} ${olderLink && newerLink ? ' | ' : ''} ${newerLink}</p>

    <p><b>${t('chat.quick_actions')}</b></p>
    <p>
      <a href="/wml/send.text.wml?to=${encodeURIComponent(jid)}" accesskey="1">${t('chat.send_text')}</a> |
      <a href="/wml/contact.wml?jid=${encodeURIComponent(jid)}" accesskey="4">${t('chat.contact_info')}</a>
      ${number && !jid.endsWith('@g.us') ? ` | <a href="wtai://wp/mc;${number}" accesskey="9">${t('chat.call')}</a>` : ''}
    </p>

    <p>
      <a href="/wml/chats.wml" accesskey="0">${t('chat.back')}</a> |
      <a href="/wml/home.wml" accesskey="*">${t('chat.home')}</a>
    </p>

    <do type="accept" label="${t('common.send')}">
      <go href="/wml/send.text.wml?to=${encodeURIComponent(jid)}"/>
    </do>
    <do type="options" label="${t('common.refresh')}">
      <go href="/wml/chat.wml?jid=${encodeURIComponent(jid)}&amp;offset=${offset}&amp;search=${encodeURIComponent(search)}"/>
    </do>
  `

  res.setHeader('Content-Type', 'text/vnd.wap.wml; charset=UTF-8')
  res.setHeader('Cache-Control', 'no-cache, no-store, must-revalidate')
  res.setHeader('Pragma', 'no-cache')
  res.setHeader('Expires', '0')
  
  res.send(`<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
  <head>
    <meta http-equiv="Cache-Control" content="no-cache, no-store"/>
  </head>
  <card id="chat" title="${escWml(chatName)}">
    ${body}
  </card>
</wml>`)
})*/

// Enhanced Status page
app.get("/wml/status.wml", (req, res) => {
  const connected = !!sock?.authState?.creds && connectionState === 'open';
  const uptime = Math.floor(process.uptime() / 60);
  const refreshNonce = Date.now();

  const body = `
    <p><b>${t('status.title')}</b></p>
    <p>${t('status.connection')} ${connected ? `<b>${t('status.active')}</b>` : `<em>${t('status.inactive')}</em>`}</p>
    <p>${t('status.state')} ${esc(connectionState)}</p>
    <p>${t('status.qr_available')} ${currentQR ? t('status.yes') : t('status.no')}</p>
    <p>${t('status.uptime')} ${uptime} ${t('status.minutes')}</p>

    <p>${t('status.sync_status')} ${
      isFullySynced ? `<b>${t('status.complete')}</b>` : `<em>${t('status.in_progress')}</em>`
    }</p>
    <p>${t('status.sync_attempts')} ${syncAttempts}</p>
    <p>${t('status.contacts')} ${contactStore.size}</p>
    <p>${t('status.chats')} ${chatStore.size}</p>
    <p>${t('status.messages')} ${messageStore.size}</p>

    <p><b>${t('status.sync_actions')}</b></p>
    <p>
      <a href="/wml/sync.full.wml" accesskey="1">${t('status.sync')}</a>
    </p>

    ${navigationBar()}

    <do type="accept" label="${t('status.refresh')}">
      <go href="/wml/status.wml?_rt=${refreshNonce}"/>
    </do>
  `;

  sendWml(res, card("status", t('status.title'), body, "/wml/status.wml"));
});

// Enhanced QR Code page
app.get("/wml/qr.wml", (req, res) => {
  const isConnected = !!sock?.authState?.creds && connectionState === 'open';

  // Debug log
  logger.info(`QR page accessed - isConnected: ${isConnected}, hasQR: ${!!currentQR}, connectionState: ${connectionState}, QR length: ${currentQR?.length || 0}`);

  const body = isConnected
    ? `
      <p>${t('qr.connected')}</p>
      <p>${t('qr.logged_in')}</p>
      <p>
        <a href="/wml/home.wml">${t('qr.go_home')}</a>
      </p>
      <p>
        <a href="/wml/logout.wml">${t('qr.logout')}</a>
      </p>
    `
    : currentPairingCode
    ? `
      <p><b>${t('qr.pairing_code')}</b></p>
      <p><b>${esc(currentPairingCode)}</b></p>
      <p>${t('qr.pairing_instructions')}</p>
      <p>${t('qr.pairing_enter_code')}</p>
      <p>${t('qr.status')} ${esc(connectionState)}</p>
      <p>
        <a href="/wml/qr.wml">${t('qr.refresh')}</a>
      </p>
    `
    : currentQR
    ? `
      <p>${t('qr.ready')}</p>
      <p>${t('qr.view_pc')}</p>
      <p>
        <a href="http://localhost:${port}/api/qr/image?format=png">${t('qr.open_image')}</a>
      </p>
      <p>${t('qr.scan_phone')}</p>
      <p>
        <a href="/api/qr/image?format=png">${t('qr.view_slow')}</a>
      </p>
      <p>
        <a href="/wml/qr-text.wml">${t('qr.qr_as_text')}</a>
      </p>
      <p>
        <a href="/wml/qr-wap.wml">QR Code WMB into page</a>
      </p>
      <p>
        <a href="/wml/pairing.wml">${t('qr.pairing_link')}</a>
      </p>
      <p>${t('qr.status')} ${esc(connectionState)}</p>
    `
    : sock?.authState?.creds
    ? `
      <p>${t('qr.connecting')}</p>
      <p>${t('qr.status')} ${esc(connectionState)}</p>
      <p>${t('qr.loading')}</p>
      <p>
        <a href="/wml/qr.wml">${t('qr.refresh')}</a>
      </p>
      <p>
        <a href="/wml/home.wml">${t('qr.go_home')}</a>
      </p>
      <p>
        <a href="/wml/logout.wml">${t('qr.logout_first')}</a>
      </p>
    `
    : `
      <p>${t('qr.connecting')}</p>
      <p>${t('qr.status')} ${esc(connectionState)}</p>
      <p>${t('qr.loading')}</p>
      <p>${t('qr.wait')}</p>
      <p>
        <a href="/wml/qr.wml">${t('qr.refresh')}</a>
      </p>
    `;

  const body_full = `
    ${body}
    ${isDev ? `<p>Port ${port}</p><p><small>Debug: QR=${currentQR ? 'YES' : 'NO'} State=${connectionState}</small></p>` : ''}
    <do type="accept" label="${t('common.refresh')}">
      <go href="/wml/qr.wml"/>
    </do>
  `;

  sendWml(res, card("qr", t('qr.title'), body_full));
});

app.get("/api/qr/wml-wbmp", (req, res) => {
  const isConnected = !!sock?.authState?.creds && connectionState === 'open';
  function sendRawWml(wmlStr) {
    return sendRawWmlAware(res, wmlStr);
  }

  if (isConnected) {
    return sendRawWml(`<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.0//EN" "http://www.wapforum.org/DTD/wml_1.0.xml">
<wml>
  <card id="connected" title="WhatsApp">
    <p>WhatsApp Connected</p>
    <p>You are logged in</p>
    <p><a href="/wml/home.wml">Go to Home</a></p>
  </card>
</wml>`);
  }

  if (!currentQR) {
    return sendRawWml(`<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.0//EN" "http://www.wapforum.org/DTD/wml_1.0.xml">
<wml>
  <card id="noqr" title="QR">
    <p>Connecting...</p>
    <p>QR code loading</p>
    <p>Please wait</p>
    <do type="accept" label="${t('common.refresh')}"><go href="/api/qr/wml-wbmp"/></do>
  </card>
</wml>`);
  }

  // WAP 1.0 compatible page with WBMP QR code
  sendRawWml(`<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.0//EN" "http://www.wapforum.org/DTD/wml_1.0.xml">
<wml>
  <card id="qr" title="WhatsApp QR">
    <p>Scan QR Code</p>
    <p>1. Open WhatsApp</p>
    <p>2. Menu - Linked Devices</p>
    <p>3. Link a Device</p>
    <p>4. Scan QR:</p>
    <p><img src="/api/qr/image?format=wbmp"/></p>
    <p>Status: ${connectionState}</p>
    <do type="accept" label="${t('common.refresh')}">
      <go href="/api/qr/wml-wbmp"/>
    </do>
  </card>
</wml>`);
});

// ============ SETTINGS PAGE ============
app.get("/wml/settings.wml", (req, res) => {
  const refreshSeconds = (getWmlRefreshTimerUnits() / 10).toFixed(1).replace(/\.0$/, "");
  const body = `
    <p><b>${t('settings.title')}</b></p>

    <p><b>${t('settings.defaults')}</b></p>
    <p>${t('settings.language_setting')} ${esc(userSettings.defaultLanguage)}<br/>
    <a href="/wml/settings-language.wml">${t('settings.change_ui_language')}</a></p>

    <p>${t('settings.tts_language')} ${esc(userSettings.defaultLanguage)}<br/>
    <a href="/wml/settings-tts.wml">${t('settings.change_language')}</a></p>

    <p>${t('settings.image_format')} ${esc(userSettings.defaultImageFormat.toUpperCase())}<br/>
    <a href="/wml/settings-format.wml?type=image">${t('settings.change')}</a></p>

    <p>${t('settings.video_format')} ${esc(userSettings.defaultVideoFormat.toUpperCase())}<br/>
    <a href="/wml/settings-format.wml?type=video">${t('settings.change')}</a></p>

    <p><b>${t('settings.display')}</b></p>
    <p>${t('settings.items_per_page')} ${userSettings.paginationLimit}<br/>
    <a href="/wml/settings-pagination.wml">${t('settings.change')}</a></p>
    <p>Auto-refresh: ${refreshSeconds}s<br/>
    <a href="/wml/settings-refresh.wml">${t('settings.change')}</a></p>

    <p><b>${t('settings.favorites')}</b></p>
    <p>${userSettings.favorites.length} ${t('settings.contacts_count')}<br/>
    <a href="/wml/favorites.wml">${t('settings.manage')}</a></p>

    <p><b>${t('settings.wap_push')}</b></p>
    <p>${t('settings.wap_push_status')} ${userSettings.wapPushEnabled ? t('common.yes') : t('common.no')}${userSettings.wapPushPhone ? ' (' + esc(userSettings.wapPushPhone) + ')' : ''}<br/>
    <a href="/wml/settings-wappush.wml">${t('settings.change')}</a></p>

    <p><b>${t('settings.about')}</b></p>
    <p>${t('settings.version')}<br/>
    ${t('settings.for_device')}<br/>
    <a href="/wml/help.wml">${t('settings.help_guide')}</a></p>

    <p><a href="/wml/home.wml" accesskey="0">${t('settings.home')}</a></p>

    <do type="accept" label="${t('home.title')}">
      <go href="/wml/home.wml"/>
    </do>
  `;

  sendWml(res, card("settings", t('settings.title'), body));
});

// Settings - Auto refresh timer (WML timer units: 10 = 1s)
app.post("/wml/settings-refresh.wml", (req, res) => {
  const { units } = req.body;
  userSettings.refreshTimerUnits = normalizeWmlRefreshUnits(units);
  saveSettings();
  authRedirect(res, "/wml/settings.wml");
});

app.get("/wml/settings-refresh.wml", (_req, res) => {
  const currentUnits = getWmlRefreshTimerUnits();
  const currentSeconds = (currentUnits / 10).toFixed(1).replace(/\.0$/, "");
  const body = `
    <p><b>Auto-refresh Timer</b></p>
    <p>Current: ${currentUnits} units (${currentSeconds}s)</p>
    <p>Select interval:</p>
    <select name="units" title="Refresh">
      <option value="30"${currentUnits === 30 ? ' selected="selected"' : ''}>3s</option>
      <option value="50"${currentUnits === 50 ? ' selected="selected"' : ''}>5s</option>
      <option value="80"${currentUnits === 80 ? ' selected="selected"' : ''}>8s</option>
      <option value="100"${currentUnits === 100 ? ' selected="selected"' : ''}>10s</option>
      <option value="150"${currentUnits === 150 ? ' selected="selected"' : ''}>15s</option>
      <option value="200"${currentUnits === 200 ? ' selected="selected"' : ''}>20s</option>
    </select>
    <p>
      <anchor title="${t('common.save')}">${t('common.save')}
        <go method="post" href="/wml/settings-refresh.wml">
          <postfield name="units" value="$units"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.save')}">
      <go method="post" href="/wml/settings-refresh.wml">
        <postfield name="units" value="$units"/>
      </go>
    </do>
    <p><a href="/wml/settings.wml" accesskey="0">${t('common.back')}</a></p>
  `;
  sendWml(res, card("settings-refresh", "Refresh Timer", body));
});

// Settings - TTS Language
app.post("/wml/settings-tts.wml", (req, res) => {
  const { language } = req.body;
  if (language) {
    userSettings.defaultLanguage = language;
    if (req.session) req.session.lang = language;
    saveSettings();
  }
  authRedirect(res, "/wml/settings.wml");
});

app.get("/wml/settings-tts.wml", (req, res) => {
  const ttsStatus = ttsEnabled ? '✓ Ready' : '⚠ espeak not installed';
  const sttStatus = transcriptionEnabled ? '✓ Ready' : '⚠ Model not loaded';

  const body = `
    <p><b>${t('settings_tts.title')}</b></p>

    <p><b>${t('settings_tts.tts_header')}</b></p>
    <p>${t('settings_tts.tts_engine')}</p>
    <p>${t('settings_tts.tts_languages')}</p>
    <p>${t('settings_tts.status')} ${ttsStatus}</p>

    <p><b>${t('settings_tts.stt_header')}</b></p>
    <p>${t('settings_tts.stt_engine')}</p>
    <p>${t('settings_tts.tts_languages')}</p>
    <p>${t('settings_tts.status')} ${sttStatus}</p>
    <p>${t('settings_tts.stt_detection')}</p>

    <p><b>${t('settings_tts.stt_languages')}</b></p>
    <p><small>• ${t('settings_tts.english')}<br/>• ${t('settings_tts.italian')}<br/>• ${t('settings_tts.auto_detect')}</small></p>

    <p><b>${t('settings_tts.stt_quality')}</b></p>
    <p><small>${t('settings_tts.stt_model')}<br/>${t('settings_tts.high_accuracy')}<br/>${t('settings_tts.offline')}</small></p>

    <p><b>${t('settings_tts.info')}</b></p>
    <p><small>${t('settings_tts.tts_local')}<br/>${t('settings_tts.stt_whisper')}<br/>${t('settings_tts.both_offline')}</small></p>

    ${!ttsEnabled ? '<p><small>TTS: sudo apt-get install espeak</small></p>' : ''}
    ${!transcriptionEnabled ? '<p><small>STT: Whisper model loading...</small></p>' : ''}

    <p><a href="/wml/settings.wml" accesskey="0">${t('settings_tts.back')}</a></p>
  `;

  sendWml(res, card("settings-speech", t('settings_tts.title'), body));
});

// Settings - Format
app.post("/wml/settings-format.wml", (req, res) => {
  const { type, format } = req.body;
  if (type === 'image' && format) {
    userSettings.defaultImageFormat = format;
  } else if (type === 'video' && format) {
    userSettings.defaultVideoFormat = format;
  }
  saveSettings();
  authRedirect(res, "/wml/settings.wml");
});

app.get("/wml/settings-format.wml", (req, res) => {
  const type = req.query.type || 'image';
  const current = type === 'image' ? userSettings.defaultImageFormat : userSettings.defaultVideoFormat;

  const body = `
    <p><b>${t('settings_format.title')} ${esc(type.charAt(0).toUpperCase() + type.slice(1))}</b></p>
    <p>${t('settings_format.current')} ${esc(current.toUpperCase())}</p>

    <p>${t('settings_format.select')}</p>
    <select name="format" title="Format">
      <option value="wbmp"${current === 'wbmp' ? ' selected="selected"' : ''}>${t('settings_format.wbmp')}</option>
      <option value="jpg"${current === 'jpg' ? ' selected="selected"' : ''}>${t('settings_format.jpeg')}</option>
      <option value="png"${current === 'png' ? ' selected="selected"' : ''}>${t('settings_format.png')}</option>
    </select>

    <p>
      <anchor title="${t('settings_format.save')}">${t('settings_format.save')}
        <go method="post" href="/wml/settings-format.wml">
          <postfield name="type" value="${esc(type)}"/>
          <postfield name="format" value="$format"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('settings_format.save')}">
      <go method="post" href="/wml/settings-format.wml">
        <postfield name="type" value="${esc(type)}"/>
        <postfield name="format" value="$format"/>
      </go>
    </do>

    <p><a href="/wml/settings.wml" accesskey="0">${t('settings_format.back')}</a></p>
  `;

  sendWml(res, card("settings-format", t('settings_format.title'), body));
});

// Settings - Pagination
app.post("/wml/settings-pagination.wml", (req, res) => {
  const { limit } = req.body;
  if (limit) {
    userSettings.paginationLimit = parseInt(limit, 10) || 10;
    saveSettings();
  }
  authRedirect(res, "/wml/settings.wml");
});

app.get("/wml/settings-pagination.wml", (req, res) => {
  const body = `
    <p><b>${t('settings_pagination.title')}</b></p>
    <p>${t('settings_pagination.current')} ${userSettings.paginationLimit}</p>

    <p>${t('settings_pagination.select')}</p>
    <select name="limit" title="Limit">
      <option value="5"${userSettings.paginationLimit === 5 ? ' selected="selected"' : ''}>${t('settings_pagination.items_5')}</option>
      <option value="10"${userSettings.paginationLimit === 10 ? ' selected="selected"' : ''}>${t('settings_pagination.items_10')}</option>
      <option value="15"${userSettings.paginationLimit === 15 ? ' selected="selected"' : ''}>${t('settings_pagination.items_15')}</option>
      <option value="20"${userSettings.paginationLimit === 20 ? ' selected="selected"' : ''}>${t('settings_pagination.items_20')}</option>
    </select>

    <p>
      <anchor title="${t('settings_pagination.save')}">${t('settings_pagination.save')}
        <go method="post" href="/wml/settings-pagination.wml">
          <postfield name="limit" value="$limit"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('settings_pagination.save')}">
      <go method="post" href="/wml/settings-pagination.wml">
        <postfield name="limit" value="$limit"/>
      </go>
    </do>

    <p><a href="/wml/settings.wml" accesskey="0">${t('settings_pagination.back')}</a></p>
  `;

  sendWml(res, card("settings-pagination", t('settings_pagination.title'), body));
});

// ============ WAP PUSH SETTINGS ============
app.get("/wml/settings-wappush.wml", (req, res) => {
  const phoneSet = !!userSettings.wapPushPhone;
  const pushOn = !!userSettings.wapPushEnabled;
  const expOn = !!userSettings.wapPushExpireEnabled;
  const delOn = !!userSettings.wapPushDeleteEnabled;
  const histOn = !!userSettings.wapPushHistoryEnabled;
  const expSec = Math.round((userSettings.wapPushExpireMs || 120000) / 1000);
  const histLim = userSettings.wapPushHistoryLimit || 30;

  const body = `
    <p><b>${t('settings_wappush.title')}</b></p>

    <p>${t('settings_wappush.push_enabled')} ${pushOn ? t('common.yes') : t('common.no')}<br/>
    <anchor>${pushOn ? t('settings_wappush.disable_push') : t('settings_wappush.enable_push')}
      <go method="post" href="/wml/settings-wappush-toggle.wml">
        <postfield name="field" value="wapPushEnabled"/>
        <postfield name="val" value="${pushOn ? '0' : '1'}"/>
      </go>
    </anchor></p>

    <p>${t('settings_wappush.phone_label')} ${phoneSet ? esc(userSettings.wapPushPhone) : t('common.no')}</p>
    <p>
      <do type="accept" label="${t('common.save')}">
        <go method="post" href="/wml/settings-wappush.wml">
          <postfield name="phone" value="$(phone)"/>
        </go>
      </do>
      ${t('settings_wappush.set_phone')}<br/>
      <input name="phone" value="${esc(userSettings.wapPushPhone)}" format="*N" maxlength="15"/>
    </p>
    ${phoneSet ? `<p><anchor>${t('settings_wappush.clear_phone')}
      <go method="post" href="/wml/settings-wappush.wml">
        <postfield name="phone" value=""/>
      </go>
    </anchor></p>` : ''}

    <p><b>${t('settings_wappush.expiration')}</b></p>
    <p>${t('settings_wappush.expire_enabled')} ${expOn ? t('common.yes') : t('common.no')}<br/>
    <anchor>${expOn ? t('common.disable') : t('common.enable')}
      <go method="post" href="/wml/settings-wappush-toggle.wml">
        <postfield name="field" value="wapPushExpireEnabled"/>
        <postfield name="val" value="${expOn ? '0' : '1'}"/>
      </go>
    </anchor></p>
    ${expOn ? `<p>${t('settings_wappush.expire_value')} ${expSec}s<br/>
    <a href="/wml/settings-wappush-expire.wml">${t('settings.change')}</a></p>` : ''}

    <p><b>${t('settings_wappush.auto_delete')}</b></p>
    <p>${t('settings_wappush.delete_enabled')} ${delOn ? t('common.yes') : t('common.no')}<br/>
    <anchor>${delOn ? t('common.disable') : t('common.enable')}
      <go method="post" href="/wml/settings-wappush-toggle.wml">
        <postfield name="field" value="wapPushDeleteEnabled"/>
        <postfield name="val" value="${delOn ? '0' : '1'}"/>
      </go>
    </anchor></p>

    <p><b>${t('settings_wappush.history')}</b></p>
    <p>${t('settings_wappush.history_enabled')} ${histOn ? t('common.yes') : t('common.no')}<br/>
    <anchor>${histOn ? t('common.disable') : t('common.enable')}
      <go method="post" href="/wml/settings-wappush-toggle.wml">
        <postfield name="field" value="wapPushHistoryEnabled"/>
        <postfield name="val" value="${histOn ? '0' : '1'}"/>
      </go>
    </anchor></p>
    ${histOn ? `<p>${t('settings_wappush.history_limit')} ${histLim}<br/>
    <a href="/wml/settings-wappush-history.wml">${t('settings.change')}</a></p>` : ''}

    <p><a href="/wml/settings.wml" accesskey="0">${t('common.back')}</a></p>

    <do type="options" label="${t('settings.title')}">
      <go href="/wml/settings.wml"/>
    </do>
  `;
  sendWml(res, card("settings-wappush", t('settings_wappush.title'), body));
});

// WAP Push - save phone number
app.post("/wml/settings-wappush.wml", (req, res) => {
  const phone = (req.body.phone || '').trim();
  userSettings.wapPushPhone = phone;
  saveSettings();
  authRedirect(res, "/wml/settings-wappush.wml");
});

// WAP Push - toggle boolean fields
app.post("/wml/settings-wappush-toggle.wml", (req, res) => {
  const { field, val } = req.body;
  const allowed = ['wapPushEnabled', 'wapPushExpireEnabled', 'wapPushDeleteEnabled', 'wapPushHistoryEnabled'];
  if (allowed.includes(field)) {
    userSettings[field] = val === '1';
    saveSettings();
  }
  authRedirect(res, "/wml/settings-wappush.wml");
});

// WAP Push - expiration time picker
app.get("/wml/settings-wappush-expire.wml", (_req, res) => {
  const currentMs = userSettings.wapPushExpireMs || 120000;
  const currentSec = Math.round(currentMs / 1000);
  const body = `
    <p><b>${t('settings_wappush.expire_title')}</b></p>
    <p>${t('settings_wappush.expire_current')} ${currentSec}s (${currentMs}ms)</p>
    <p>${t('settings_wappush.expire_select')}</p>
    <select name="ms" title="Expiration">
      <option value="30000"${currentMs === 30000 ? ' selected="selected"' : ''}>30s</option>
      <option value="60000"${currentMs === 60000 ? ' selected="selected"' : ''}>1min</option>
      <option value="120000"${currentMs === 120000 ? ' selected="selected"' : ''}>2min</option>
      <option value="300000"${currentMs === 300000 ? ' selected="selected"' : ''}>5min</option>
      <option value="600000"${currentMs === 600000 ? ' selected="selected"' : ''}>10min</option>
      <option value="1800000"${currentMs === 1800000 ? ' selected="selected"' : ''}>30min</option>
      <option value="3600000"${currentMs === 3600000 ? ' selected="selected"' : ''}>1h</option>
    </select>
    <p>
      <anchor title="${t('common.save')}">${t('common.save')}
        <go method="post" href="/wml/settings-wappush-expire.wml">
          <postfield name="ms" value="$ms"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.save')}">
      <go method="post" href="/wml/settings-wappush-expire.wml">
        <postfield name="ms" value="$ms"/>
      </go>
    </do>
    <p><a href="/wml/settings-wappush.wml" accesskey="0">${t('common.back')}</a></p>
  `;
  sendWml(res, card("settings-wappush-expire", t('settings_wappush.expire_title'), body));
});

app.post("/wml/settings-wappush-expire.wml", (req, res) => {
  const ms = Number.parseInt(req.body.ms, 10);
  if (Number.isFinite(ms) && ms >= 10000 && ms <= 86400000) {
    userSettings.wapPushExpireMs = ms;
    saveSettings();
  }
  authRedirect(res, "/wml/settings-wappush.wml");
});

// WAP Push - history limit picker
app.get("/wml/settings-wappush-history.wml", (_req, res) => {
  const currentLimit = userSettings.wapPushHistoryLimit || 30;
  const body = `
    <p><b>${t('settings_wappush.history_title')}</b></p>
    <p>${t('settings_wappush.history_current')} ${currentLimit}</p>
    <p>${t('settings_wappush.history_select')}</p>
    <select name="limit" title="History">
      <option value="10"${currentLimit === 10 ? ' selected="selected"' : ''}>10</option>
      <option value="20"${currentLimit === 20 ? ' selected="selected"' : ''}>20</option>
      <option value="30"${currentLimit === 30 ? ' selected="selected"' : ''}>30</option>
      <option value="50"${currentLimit === 50 ? ' selected="selected"' : ''}>50</option>
      <option value="100"${currentLimit === 100 ? ' selected="selected"' : ''}>100</option>
    </select>
    <p>
      <anchor title="${t('common.save')}">${t('common.save')}
        <go method="post" href="/wml/settings-wappush-history.wml">
          <postfield name="limit" value="$limit"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.save')}">
      <go method="post" href="/wml/settings-wappush-history.wml">
        <postfield name="limit" value="$limit"/>
      </go>
    </do>
    <p><a href="/wml/settings-wappush.wml" accesskey="0">${t('common.back')}</a></p>
  `;
  sendWml(res, card("settings-wappush-history", t('settings_wappush.history_title'), body));
});

app.post("/wml/settings-wappush-history.wml", (req, res) => {
  const limit = Number.parseInt(req.body.limit, 10);
  if (Number.isFinite(limit) && limit >= 5 && limit <= 500) {
    userSettings.wapPushHistoryLimit = limit;
    saveSettings();
  }
  authRedirect(res, "/wml/settings-wappush.wml");
});

// ============ UI LANGUAGE SETTINGS ============
app.post("/wml/settings-language.wml", (req, res) => {
  const { lang } = req.body;
  if (lang && translations[lang]) {
    userSettings.defaultLanguage = lang;
    if (req.session) req.session.lang = lang;
    saveSettings();
  }
  authRedirect(res, "/wml/settings.wml");
});

app.get("/wml/settings-language.wml", (_req, res) => {
  const current = userSettings.defaultLanguage || 'en';
  const body = `
    <p><b>${t('settings_language.title')}</b></p>
    <p>${t('settings_language.current')} ${esc(current)}</p>

    <p>${t('settings_language.select')}</p>
    <select name="lang" title="Language">
      <option value="en"${current === 'en' ? ' selected="selected"' : ''}>${t('settings_language.english')}</option>
      <option value="it"${current === 'it' ? ' selected="selected"' : ''}>${t('settings_language.italian')}</option>
    </select>

    <p>
      <anchor title="${t('settings_language.save')}">${t('settings_language.save')}
        <go method="post" href="/wml/settings-language.wml">
          <postfield name="lang" value="$lang"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('settings_language.save')}">
      <go method="post" href="/wml/settings-language.wml">
        <postfield name="lang" value="$lang"/>
      </go>
    </do>

    <p><a href="/wml/settings.wml" accesskey="0">${t('settings_language.back')}</a></p>
  `;

  sendWml(res, card("settings-language", t('settings_language.title'), body));
});

// ============ HELP PAGE ============
app.get("/wml/help.wml", (req, res) => {
  const section = req.query.section || 'main';

  let body = '';

  if (section === 'main') {
    body = `
      <p><b>${t('help.title')}</b></p>

      <p><b>${t('help.quick_start')}</b></p>
      <p>1. Home has favorites &amp; recent chats<br/>
      2. Use number keys for shortcuts<br/>
      3. [0] always goes back/home<br/>
      4. Add favorites for quick access</p>

      <p><b>${t('help.topics')}</b></p>
      <p>
        <a href="/wml/help.wml?section=keys" accesskey="1">${t('help.shortcuts')}</a><br/>
        <a href="/wml/help.wml?section=messages" accesskey="2">${t('help.sending')}</a><br/>
        <a href="/wml/help.wml?section=media" accesskey="3">${t('help.media')}</a><br/>
        <a href="/wml/help.wml?section=video" accesskey="4">${t('help.video')}</a><br/>
        <a href="/wml/help.wml?section=tts" accesskey="5">${t('help.voice')}</a><br/>
        <a href="/wml/help.wml?section=favorites" accesskey="6">${t('help.favorites')}</a><br/>
        <a href="/wml/help.wml?section=tips" accesskey="7">${t('help.tips')}</a><br/>
        <a href="/wml/help.wml?section=setup" accesskey="8">${t('help.setup')}</a>
      </p>

      <p><a href="/wml/home.wml" accesskey="0">${t('help.home')}</a></p>
    `;
  } else if (section === 'keys') {
    body = `
      <p><b>${t('help.shortcuts')}</b></p>

      <p><b>Home Screen:</b></p>
      <p>[1] ${t('contacts.title')} | [2] ${t('chats.title')}<br/>
      [3] ${t('send_menu.send')} | [4] ${t('groups.title')}<br/>
      [5] ${t('search.title')} | [6] ${t('settings.title')}<br/>
      [7] ${t('help.title')} | [8] ${t('profile.title')}<br/>
      [9] ${t('status.title')} | [0] ${t('logout.title')}</p>

      <p><b>Universal:</b></p>
      <p>[0] Back / Home<br/>
      [*] Quick action<br/>
      [#] Options menu</p>

      <p><a href="/wml/help.wml" accesskey="0">${t('common.back')}</a></p>
    `;
  } else if (section === 'messages') {
    body = `
      <p><b>${t('help.sending')}</b></p>

      <p><b>Types:</b></p>
      <p>1. ${t('send_menu.text')}<br/>
      2. ${t('send_menu.voice')}<br/>
      3. ${t('send_menu.image')}<br/>
      4. ${t('send_menu.video')}<br/>
      5. ${t('send_menu.audio')}<br/>
      6. ${t('send_menu.location')}<br/>
      7. ${t('send_menu.contact')}<br/>
      8. ${t('send_menu.poll')}</p>

      <p><b>Quick Send:</b></p>
      <p>From Home: [3] ${t('send_menu.send')}<br/>
      Select contact &amp; type</p>

      <p><a href="/wml/help.wml" accesskey="0">${t('common.back')}</a></p>
    `;
  } else if (section === 'media') {
    body = `
      <p><b>${t('help.media')}</b></p>

      <p><b>Format Selection:</b></p>
      <p>Images &amp; Videos support:<br/>
      - WBMP: B&amp;W, smallest<br/>
      - JPEG: Color, medium<br/>
      - PNG: Color, high quality</p>

      <p><b>Change Format:</b></p>
      <p>During viewing, press [7]<br/>
      Or set default in ${t('settings.title')}</p>

      <p><b>Download:</b></p>
      <p>View media info page<br/>
      Select download format</p>

      <p><a href="/wml/help.wml" accesskey="0">${t('common.back')}</a></p>
    `;
  } else if (section === 'video') {
    body = `
      <p><b>${t('help.video')}</b></p>

      <p><b>How it works:</b></p>
      <p>Videos play frame-by-frame<br/>
      1 frame per second<br/>
      Perfect for WAP devices!</p>

      <p><b>Controls:</b></p>
      <p>[4] Previous frame<br/>
      [5] Play / Auto-play<br/>
      [6] Next frame<br/>
      [7] Change format<br/>
      [0] Back</p>

      <p><b>Formats:</b></p>
      <p>WBMP: Fast, tiny files<br/>
      JPEG/PNG: Color, larger</p>

      <p><a href="/wml/help.wml" accesskey="0">${t('common.back')}</a></p>
    `;
  } else if (section === 'tts') {
    body = `
      <p><b>${t('help.voice')}</b></p>

      <p><b>Text-to-Speech:</b></p>
      <p>Type text on your Nokia<br/>
      Converts to voice message<br/>
      Sends as WhatsApp audio!</p>

      <p><b>Features:</b></p>
      <p>- 15 languages supported<br/>
      - Up to 500 characters<br/>
      - Voice note or audio file<br/>
      - Free Google TTS</p>

      <p><b>Usage:</b></p>
      <p>Send Menu &gt; Voice (TTS)<br/>
      Type message &gt; ${t('common.send')}</p>

      <p><b>Default Language:</b></p>
      <p>Set in ${t('settings.title')} &gt; ${t('settings.tts_language')}</p>

      <p><a href="/wml/help.wml" accesskey="0">${t('common.back')}</a></p>
    `;
  } else if (section === 'favorites') {
    body = `
      <p><b>${t('help.favorites')}</b></p>

      <p><b>Quick Access:</b></p>
      <p>Add contacts to favorites<br/>
      Appears on home screen<br/>
      One-tap chat access</p>

      <p><b>Add Favorite:</b></p>
      <p>1. Open contact<br/>
      2. Select ${t('contact.add_favorite')}<br/>
      3. See on home screen</p>

      <p><b>Manage:</b></p>
      <p>${t('settings.title')} &gt; ${t('settings.favorites')}<br/>
      View all &amp; remove</p>

      <p><a href="/wml/help.wml" accesskey="0">${t('common.back')}</a></p>
    `;
  } else if (section === 'tips') {
    body = `
      <p><b>${t('help.tips')}</b></p>

      <p><b>Speed Tips:</b></p>
      <p>1. Use keyboard shortcuts<br/>
      2. Add frequent contacts to favorites<br/>
      3. Set WBMP as default format<br/>
      4. Use TTS for quick voice msgs</p>

      <p><b>Data Saving:</b></p>
      <p>- Use WBMP format<br/>
      - Reduce items per page<br/>
      - Disable auto-refresh</p>

      <p><b>Best Practices:</b></p>
      <p>- Sync when on WiFi<br/>
      - Keep favorites updated<br/>
      - Use search for old msgs</p>

      <p><a href="/wml/help.wml" accesskey="0">${t('common.back')}</a></p>
    `;
  } else if (section === 'setup') {
    body = `
      <p><b>${t('help.setup')}</b></p>

      <p><b>1. WhatsApp Pairing:</b></p>
      <p>Link your WhatsApp account:<br/>
      Open /wml/qr.wml on a browser<br/>
      Scan QR with WhatsApp app<br/>
      (Linked Devices &gt; Link)</p>

      <p><b>Pairing Code (alt):</b></p>
      <p>Set WA_PHONE_NUMBER env var<br/>
      with your full number + country<br/>
      code (e.g. 391234567890)<br/>
      Enter the 6-digit code shown</p>

      <p><b>2. App Login:</b></p>
      <p>Default: admin / admin<br/>
      Change password in Settings!<br/>
      Or set AUTH_ENABLED=false<br/>
      to disable login</p>

      <p><b>3. WAP Push (optional):</b></p>
      <p>Needs NowSMS gateway<br/>
      Set WAP_PUSH_BASE_URL,<br/>
      WAP_PUSH_AUTH, WAP_PUSH_PHONE<br/>
      in .env file or Settings</p>

      <p><b>4. After Reboot:</b></p>
      <p>Session auto-restores<br/>
      No re-pairing needed<br/>
      Unless you log out from WA</p>

      <p><a href="/wml/help.wml" accesskey="0">${t('common.back')}</a></p>
    `;
  }

  sendWml(res, card("help", t('help.title'), body));
});

// ============ FAVORITES PAGE ============
app.get("/wml/favorites.wml", (req, res) => {
  let body = `<p><b>${t('favorites.title')}</b></p>`;

  if (userSettings.favorites.length === 0) {
    body += `<p>${t('favorites.empty')}<br/>
    ${t('favorites.hint')}</p>
    <p>
      <a href="/wml/contacts.wml">${t('favorites.contacts_link')}</a> |
      <a href="/wml/groups.wml">${t('favorites.groups_link')}</a>
    </p>`;
  } else {
    // Separate contacts and groups
    const contactFavs = [];
    const groupFavs = [];

    for (const jid of userSettings.favorites) {
      if (jid.endsWith('@g.us')) {
        groupFavs.push(jid);
      } else {
        contactFavs.push(jid);
      }
    }

    body += `<p>${t('favorites.total')} ${userSettings.favorites.length} (${contactFavs.length} ${t('favorites.contacts')}, ${groupFavs.length} ${t('favorites.groups')})</p>`;

    // Show contacts
    if (contactFavs.length > 0) {
      body += `<p><b>${t('favorites.contacts_header')}</b></p>`;
      for (let i = 0; i < contactFavs.length; i++) {
        const jid = contactFavs[i];
        const contact = contactStore.get(jid);
        const name = contact?.name || contact?.notify || jidFriendly(jid);
        const accessKey = i < 9 ? ` accesskey="${i + 1}"` : '';
        body += `<p>
          <a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}"${accessKey}>${i < 9 ? `[${i + 1}] ` : ''}${esc(name)}</a><br/>
          <a href="/wml/contact.wml?jid=${encodeURIComponent(jid)}">${t('favorites.info')}</a> |
          <a href="/wml/favorites-remove.wml?jid=${encodeURIComponent(jid)}">${t('favorites.remove')}</a>
        </p>`;
      }
    }

    // Show groups
    if (groupFavs.length > 0) {
      body += `<p><b>${t('favorites.groups_header')}</b></p>`;
      for (const jid of groupFavs) {
        const contact = contactStore.get(jid);
        const name = contact?.name || contact?.subject || jidFriendly(jid);
        body += `<p>
          <a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}">${esc(name)}</a><br/>
          <a href="/wml/group.view.wml?gid=${encodeURIComponent(jid)}">${t('favorites.info')}</a> |
          <a href="/wml/favorites-remove.wml?jid=${encodeURIComponent(jid)}">${t('favorites.remove')}</a>
        </p>`;
      }
    }
  }

  body += `
    <p><b>${t('favorites.actions')}</b></p>
    <p>
      <a href="/wml/contacts.wml">${t('favorites.browse_contacts')}</a><br/>
      <a href="/wml/groups.wml">${t('favorites.browse_groups')}</a>
    </p>
    <p><a href="/wml/home.wml" accesskey="0">${t('favorites.home')}</a></p>
  `;

  sendWml(res, card("favorites", t('favorites.title'), body));
});

// Remove from favorites
app.get("/wml/favorites-remove.wml", (req, res) => {
  const jid = req.query.jid;
  const back = req.query.back || "favorites";

  if (jid) {
    removeFavorite(jid);
  }

  // Smart redirect based on 'back' parameter
  const redirectMap = {
    contact: `/wml/contact.wml?jid=${encodeURIComponent(jid)}`,
    group: `/wml/group.view.wml?gid=${encodeURIComponent(jid)}`,
    chat: `/wml/chat.wml?jid=${encodeURIComponent(jid)}`,
    favorites: "/wml/favorites.wml"
  };

  authRedirect(res, redirectMap[back] || "/wml/favorites.wml");
});

// Add to favorites
app.get("/wml/favorites-add.wml", (req, res) => {
  const jid = req.query.jid;
  const back = req.query.back || "chat";
  let message = "Error";
  let linkBack = "/wml/contacts.wml";

  if (jid) {
    const isGroup = jid.endsWith('@g.us');

    if (addFavorite(jid)) {
      const contact = contactStore.get(jid);
      const name = contact?.name || contact?.notify || contact?.subject || jidFriendly(jid);
      message = `${esc(name)} added to favorites!`;

      // Smart back link based on context
      if (back === "contact") {
        linkBack = `/wml/contact.wml?jid=${encodeURIComponent(jid)}`;
      } else if (back === "group") {
        linkBack = `/wml/group.view.wml?gid=${encodeURIComponent(jid)}`;
      } else if (back === "chat") {
        linkBack = `/wml/chat.wml?jid=${encodeURIComponent(jid)}`;
      }
    } else {
      message = "Already in favorites";
      linkBack = `/wml/favorites.wml`;
    }
  }

  const body = `
    <p><b>${message}</b></p>
    <p>
      <a href="${linkBack}" accesskey="1">[1] Back</a><br/>
      <a href="/wml/favorites.wml" accesskey="2">[2] View Favorites</a><br/>
      <a href="/wml/home.wml" accesskey="0">[0] Home</a>
    </p>
  `;

  sendWml(res, card("fav-add", "Success", body));
});

// Enhanced Contacts with search and pagination

app.get("/wml/contacts.wml", (req, res) => {
  const userAgent = req.headers["user-agent"] || "";

  // Usa req.query per GET. Se il form usa POST, i dati sarebbero in req.body.
  // La <go> con method="get" mette i dati in query string.
  const query = req.query;

  const page = Math.max(1, parseInt(query.page || "1"));
  let limit = 3; // Fisso a 3 elementi per pagina

  // Limiti più restrittivi per dispositivi WAP 1.0

    limit = Math.min(3, limit); // Max 3 elementi per pagina


  const search = query.q || "";
  const refreshNonce = Date.now();

  // ULTRA-PERFORMANCE: Use pre-sorted cache (instant response)
  // Build sorted index only once or when data changes
  perfCache.getSortedContacts(contactStore, chatStore);

  // Get paginated results instantly (no sorting needed!)
  const { items: paginatedItems, total } =
    perfCache.paginateContacts(page, limit, search);

  const start = (page - 1) * limit;
  const items = paginatedItems.map(c => c.contact);

  // Funzione di escaping sicura per WML
  // Uses global escWml — single-pass O(L) instead of O(5L)

  // Header della pagina
  const searchHeader = search
    ? `<p><b>${t('contacts.results_for')}</b> ${escWml(search)} (${total})</p>`
    : `<p><b>${t('contacts.all')}</b> (${total})</p>`;

  // Lista contatti
  const list =
    items
      .map((c, idx) => {
        const name = c.name || c.notify || c.verifiedName || t('contacts.unknown');
        const jid = c.id;
        const number = jidFriendly(jid);
        return `<p>${start + idx + 1}. ${escWml(name)}<br/>
      <small>${escWml(number)}</small><br/>
      <a href="/wml/contact.wml?jid=${encodeURIComponent(jid)}">${t('contacts.details')}</a>
      <a href="/wml/chat.wml?jid=${encodeURIComponent(
        jid
      )}&amp;limit=3">${t('contacts.chat')}</a></p>`;
      })
      .join("") || `<p>${t('contacts.not_found')}</p>`;

  // Paginazione con First/Last e numeri di pagina
  const totalPages = Math.ceil(total / limit) || 1;

  const firstPage =
    page > 1
      ? `<a href="/wml/contacts.wml?page=1&amp;limit=${limit}&amp;q=${encodeURIComponent(
          search
        )}">${t('contacts.first')}</a>`
      : "";

  const prevPage =
    page > 1
      ? `<a href="/wml/contacts.wml?page=${
          page - 1
        }&amp;limit=${limit}&amp;q=${encodeURIComponent(search)}">${t('contacts.prev')}</a>`
      : "";

  const nextPage =
    page < totalPages
      ? `<a href="/wml/contacts.wml?page=${
          page + 1
        }&amp;limit=${limit}&amp;q=${encodeURIComponent(search)}">${t('contacts.next')}</a>`
      : "";

  const lastPage =
    page < totalPages
      ? `<a href="/wml/contacts.wml?page=${totalPages}&amp;limit=${limit}&amp;q=${encodeURIComponent(
          search
        )}">${t('contacts.last')}</a>`
      : "";

  // numeri di pagina (mostra ±2 intorno alla pagina corrente)
  let pageNumbers = "";
  const startPage = Math.max(1, page - 2);
  const endPage = Math.min(totalPages, page + 2);
  for (let p = startPage; p <= endPage; p++) {
    if (p === page) {
      pageNumbers += `<b>[${p}]</b> `;
    } else {
      pageNumbers += `<a href="/wml/contacts.wml?page=${p}&amp;limit=${limit}&amp;q=${encodeURIComponent(
        search
      )}">${p}</a> `;
    }
  }

  const pagination = `
    <p>
      ${firstPage} ${firstPage && prevPage ? "" : ""} ${prevPage}
      ${pageNumbers}
      ${nextPage} ${nextPage && lastPage ? "" : ""} ${lastPage}
    </p>`;

  // Form di ricerca semplificato
  const searchForm = `
    <p><b>${t('contacts.search')}</b></p>
    <p>
      <input name="q" title="${t('contacts.search_placeholder')}" value="${escWml(
        search
      )}" emptyok="true" size="15" maxlength="30"/>
    </p>
    <p>
      <anchor title="${t('contacts.search_btn')}">${t('contacts.search_btn')}
        <go href="/wml/contacts.wml" method="get">
          <postfield name="q" value="$(q)"/>
          <postfield name="page" value="1"/>
          <postfield name="limit" value="${limit}"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('contacts.search_btn')}">
      <go href="/wml/contacts.wml" method="get">
        <postfield name="q" value="$(q)"/>
        <postfield name="page" value="1"/>
        <postfield name="limit" value="${limit}"/>
      </go>
    </do>`;

  // Corpo della card WML
  const body = `
    <p><b>${t('contacts.page_title')} ${page}/${Math.ceil(total / limit) || 1}</b></p>
    ${searchHeader}
    ${searchForm}
    ${list}
    ${pagination}
    <p>
      <a href="/wml/home.wml">${t('contacts.home')}</a>
      <a href="/wml/chats.wml">${t('contacts.chats')}</a>
    </p>
    <do type="accept" label="${t('contacts.refresh')}">
      <go href="/wml/contacts.wml?page=${page}&amp;limit=${limit}&amp;q=${encodeURIComponent(
    search
  )}&amp;_rt=${refreshNonce}"/>
    </do>
   `;

  // Crea la stringa WML completa
  const wmlOutput = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
  <head>
    <meta http-equiv="Cache-Control" content="no-cache, no-store"/>
  </head>
  <card id="contacts" title="${t('contacts.title')}" ontimer="/wml/contacts.wml?_rt=${refreshNonce}">
    <onevent type="ontimer">
      <go href="/wml/contacts.wml?_rt=${refreshNonce}"/>
    </onevent>
    <timer value="${getWmlRefreshTimerUnits()}"/>
    ${body}
  </card>
</wml>`;

  sendRawWmlAware(res, wmlOutput);
});

// Enhanced Contact Detail page with WTAI integration
app.get("/wml/contact.wml", async (req, res) => {
  try {
    if (!sock) throw new Error("Not connected");
    const jid = formatJid(req.query.jid || "");
    const contact = contactStore.get(jid);
    const number = jidFriendly(jid);

    // Try to fetch additional info
    let status = null;
    let businessProfile = null;

    try {
      status = await sock.fetchStatus(jid);
      businessProfile = await sock.getBusinessProfile(jid);
    } catch (e) {
      // Silently fail for these optional features
    }

    const body = `
      <p><b>${esc(
        contact?.name ||
          contact?.notify ||
          contact?.verifiedName ||
          "Unknown Contact"
      )}</b></p>
      <p>${t('contact.number')} ${esc(number)}</p>
      <p>${t('contact.jid')} <small>${esc(jid)}</small></p>
      ${status ? `<p>${t('contact.status')} <em>${esc(status.status || "")}</em></p>` : ""}
      ${businessProfile ? `<p><b>${t('contact.business')}</b></p>` : ""}

      <p><b>${t('contact.quick_actions')}</b></p>
      <p>
        <a href="wtai://wp/mc;${number}" accesskey="1">${t('contact.call')}</a><br/>
        <a href="wtai://wp/sms;${number};" accesskey="2">${t('contact.sms')}</a><br/>
        <a href="wtai://wp/ap;${esc(
          contact?.name || number
        )};${number}" accesskey="3">${t('contact.add_phone')}</a><br/>
      </p>

      <p><b>${t('contact.wa_actions')}</b></p>
      <p>
        <a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}&amp;limit=3" accesskey="4">${t('contact.open_chat')}</a><br/>
        <a href="/wml/send-quick.wml?to=${encodeURIComponent(
          jid
        )}" accesskey="5">${t('contact.send_message')}</a><br/>
        ${
          isFavorite(jid)
            ? `<a href="/wml/favorites-remove.wml?jid=${encodeURIComponent(
                jid
              )}&amp;back=contact" accesskey="6">${t('contact.remove_favorite')}</a><br/>`
            : `<a href="/wml/favorites-add.wml?jid=${encodeURIComponent(
                jid
              )}&amp;back=contact" accesskey="6">${t('contact.add_favorite')}</a><br/>`
        }
        <a href="/wml/block.wml?jid=${encodeURIComponent(
          jid
        )}" accesskey="7">${t('contact.block')}</a><br/>
        <a href="/wml/unblock.wml?jid=${encodeURIComponent(
          jid
        )}" accesskey="8">${t('contact.unblock')}</a><br/>
      </p>

      ${navigationBar()}

      <do type="accept" label="${t('chats.title')}">
        <go href="/wml/chat.wml?jid=${encodeURIComponent(jid)}&amp;limit=3"/>
      </do>
      <do type="options" label="${t('contact.call')}">
        <go href="wtai://wp/mc;${number}"/>
      </do>
    `;

    sendWml(res, card("contact", t('contact.unknown'), body));
  } catch (e) {
    sendWml(
      res,
      resultCard(
        "Error",
        [e.message || "Failed to load contact"],
        "/wml/contacts.wml"
      )
    );
  }
});

// =================== BLOCK/UNBLOCK WML ROUTES ===================

app.get("/wml/block.wml", async (req, res) => {
  const jid = req.query.jid || "";
  if (!jid) {
    return sendWml(res, resultCard("Error", ["No contact specified"], "/wml/contacts.wml"));
  }
  const displayName = jidFriendly(jid);
  const body = `
    <p><b>Block Contact</b></p>
    <p>Block ${esc(displayName)}?</p>
    <p><small>They will not be able to message you.</small></p>
    <p>
      <anchor title="Block">Yes, Block
        <go method="post" href="/wml/block">
          <postfield name="jid" value="${esc(jid)}"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.block')}">
      <go method="post" href="/wml/block">
        <postfield name="jid" value="${esc(jid)}"/>
      </go>
    </do>
    <p><a href="/wml/contact.wml?jid=${encodeURIComponent(jid)}" accesskey="0">[0] Cancel</a></p>
  `;
  sendWml(res, card("block", "Block Contact", body));
});

app.post("/wml/block", async (req, res) => {
  const { jid } = req.body;
  try {
    if (!sock) throw new Error("Not connected");
    await sock.updateBlockStatus(formatJid(jid), "block");
    sendWml(res, resultCard("Blocked", [`${jidFriendly(jid)} has been blocked`], "/wml/contacts.wml"));
  } catch (e) {
    sendWml(res, resultCard("Error", [e.message || "Block failed"], `/wml/contact.wml?jid=${encodeURIComponent(jid)}`));
  }
});

app.get("/wml/unblock.wml", async (req, res) => {
  const jid = req.query.jid || "";
  if (!jid) {
    return sendWml(res, resultCard("Error", ["No contact specified"], "/wml/privacy.wml"));
  }
  const displayName = jidFriendly(jid);
  const body = `
    <p><b>Unblock Contact</b></p>
    <p>Unblock ${esc(displayName)}?</p>
    <p>
      <anchor title="Unblock">Yes, Unblock
        <go method="post" href="/wml/unblock">
          <postfield name="jid" value="${esc(jid)}"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.unblock')}">
      <go method="post" href="/wml/unblock">
        <postfield name="jid" value="${esc(jid)}"/>
      </go>
    </do>
    <p><a href="/wml/blocked.list.wml" accesskey="0">[0] Cancel</a></p>
  `;
  sendWml(res, card("unblock", "Unblock Contact", body));
});

app.post("/wml/unblock", async (req, res) => {
  const { jid } = req.body;
  try {
    if (!sock) throw new Error("Not connected");
    await sock.updateBlockStatus(formatJid(jid), "unblock");
    sendWml(res, resultCard("Unblocked", [`${jidFriendly(jid)} has been unblocked`], "/wml/blocked.list.wml"));
  } catch (e) {
    sendWml(res, resultCard("Error", [e.message || "Unblock failed"], `/wml/blocked.list.wml`));
  }
});

/*
app.get('/wml/chat.wml', async (req, res) => {
  const userAgent = req.headers['user-agent'] || ''
  const isOldNokia = /Nokia|Series40|MAUI|UP\.Browser/i.test(userAgent)
  
  const raw = req.query.jid || ''
  const jid = formatJid(raw)
  const offset = Math.max(0, parseInt(req.query.offset || '0'))
  const search = (req.query.search || '').trim().toLowerCase()
  
  // Very small limits for Nokia 7210
  const limit = 3
  
  // Chat history is loaded from persistent storage on startup
  // No need to fetch from WhatsApp servers every time
  
  // Messages stored oldest→newest. For "most recent first" without O(M) copy+reverse:
  const rawMessages = chatStore.get(jid) || [];
  let allMessages, total, items;
  if (search) {
    // Search needs full scan — filter using cached lowercase text
    const searchL = search.toLowerCase();
    allMessages = [];
    for (let i = rawMessages.length - 1; i >= 0; i--) {
      const txt = getMessageSearchText(rawMessages[i]);
      if (txt.includes(searchL)) allMessages.push(rawMessages[i]);
    }
    total = allMessages.length;
    items = allMessages.slice(offset, offset + limit);
  } else {
    // No search: compute reverse window directly — O(limit) instead of O(M)
    total = rawMessages.length;
    const revStart = total - 1 - offset;
    const revEnd = Math.max(-1, revStart - limit);
    items = [];
    for (let i = revStart; i > revEnd && i >= 0; i--) {
      items.push(rawMessages[i]);
    }
  }
  
  const contact = contactStore.get(jid)
  const chatName = contact?.name || contact?.notify || contact?.verifiedName || jidFriendly(jid)
  const number = jidFriendly(jid)
  const isGroup = jid.endsWith('@g.us')
  
  // Simple escaping for Nokia 7210
  const esc = text => (text || '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
  
  // Simple truncate
  const truncate = (text, maxLength) => {
    if (!text) return ''
    if (text.length <= maxLength) return text
    return text.substring(0, maxLength - 3) + '...'
  }
  
  // Simple timestamp for Nokia
  const formatTime = (timestamp) => {
    const date = new Date(Number(timestamp) * 1000)
    if (isNaN(date.getTime())) return ''

    const day = date.getDate().toString().padStart(2, '0')
    const month = (date.getMonth() + 1).toString().padStart(2, '0')
    const year = date.getFullYear()
    const hours = date.getHours().toString().padStart(2, '0')
    const mins = date.getMinutes().toString().padStart(2, '0')
    const secs = date.getSeconds().toString().padStart(2, '0')

    return `${day}/${month}/${year} ${hours}:${mins}:${secs}`
  }
  
  let messageList = ''
  
  if (items.length === 0) {
    messageList = '<p>No messages</p>'
  } else {
    messageList = items.map((m, idx) => {
      const who = m.key.fromMe ? 'Me' : (chatName.length > 10 ? chatName.substring(0, 10) : chatName)
      const time = formatTime(m.messageTimestamp)
      const msgNumber = idx + 1
      const mid = m.key.id
      
      // Handle different message types for Nokia
      let text = ''
      let mediaLink = ''
      
      if (m.message) {
        if (m.message.imageMessage) {
          const img = m.message.imageMessage
          const size = Math.round((img.fileLength || 0) / 1024)
          text = `[IMG ${size}KB]`
          if (img.caption) text += ` ${truncate(img.caption, 30)}`
          mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}">[View IMG]</a>`
          
        } else if (m.message.videoMessage) {
          const vid = m.message.videoMessage
          const size = Math.round((vid.fileLength || 0) / 1024)
          text = `[VID ${size}KB]`
          if (vid.caption) text += ` ${truncate(vid.caption, 30)}`
          mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}">[View VID]</a>`
          
        } else if (m.message.audioMessage) {
          const aud = m.message.audioMessage
          const size = Math.round((aud.fileLength || 0) / 1024)
          const duration = aud.seconds || 0
          text = `[AUD ${size}KB ${duration}s]`
          // Show transcription preview if available
          if (m.transcription && m.transcription !== '[Trascrizione fallita]' && m.transcription !== '[Audio troppo lungo per la trascrizione]') {
            text += `<br/><small>${truncate(m.transcription, 60)}</small>`
          }
          mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}">[View AUD]</a>` +
            ` <a href="/wml/media/${encodeURIComponent(mid)}.mp3">[MP3]</a>` +
            ` <a href="/wml/media/${encodeURIComponent(mid)}.amr">[AMR]</a>`
          
        } else if (m.message.documentMessage) {
          const doc = m.message.documentMessage
          const size = Math.round((doc.fileLength || 0) / 1024)
          const filename = doc.fileName || 'file'
          text = `[DOC ${size}KB] ${truncate(filename, 20)}`
          mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}">[View DOC]</a>`
          
        } else if (m.message.stickerMessage) {
          text = '[STICKER]'
          mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}">[View STK]</a>`
          
        } else {
          text = truncate(messageText(m) || '', 50)
        }
      } else {
        text = truncate(messageText(m) || '', 50)
      }
      
      return `<p>${msgNumber}. ${esc(who)} (${time})<br/>${esc(text)}${mediaLink}</p>`
    }).join('')
  }
  
  // Simple navigation for Nokia
  const olderOffset = offset + limit
  const olderLink = olderOffset < total ? 
    `<p><a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}&amp;offset=${olderOffset}&amp;search=${encodeURIComponent(search)}" accesskey="2">2-Older</a></p>` : ''
  
  const newerOffset = Math.max(0, offset - limit)
  const newerLink = offset > 0 ? 
    `<p><a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}&amp;offset=${newerOffset}&amp;search=${encodeURIComponent(search)}" accesskey="3">3-Newer</a></p>` : ''
  
  // Simple search for Nokia
  const searchBox = search ? 
    `<p>Search: ${esc(search)}</p><p><a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}">Clear</a></p>` : 
    `<p><a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}&amp;search=prompt">Search</a></p>`
  
  const body = `<p>${esc(chatName.length > 15 ? chatName.substring(0, 15) : chatName)}</p>
<p>Msgs ${offset + 1}-${Math.min(offset + limit, total)}/${total}</p>
${searchBox}
${messageList}
${newerLink}
${olderLink}
<p><a href="/wml/send.text.wml?to=${encodeURIComponent(jid)}" accesskey="1">1-Send</a></p>
<p><a href="/wml/chats.wml" accesskey="0">0-Back</a></p>`
  
  // Nokia 7210 compatible WML 1.1
  const wmlOutput = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
<head><meta http-equiv="Cache-Con\l" content="no-cache, no-store"/></head>
<card id="chat" title="Chat">
${body}
</card>
</wml>`
  
  // Nokia 7210 headers
  res.setHeader('Content-Type', 'text/vnd.wap.wml; charset=iso-8859-1')
  res.setHeader('Cache-Control', 'no-cache')
  res.setHeader('Pragma', 'no-cache')
  
  const encodedBuffer = iconv.encode(wmlOutput, 'iso-8859-1')
  res.send(encodedBuffer)
})*/
/*
// Route per scaricare media - compatibile Nokia 7210
app.get('/wml/chat.wml', async (req, res) => {
  const userAgent = req.headers['user-agent'] || ''
  const isOldNokia = /Nokia|Series40|MAUI|UP\.Browser/i.test(userAgent)
  
  const raw = req.query.jid || ''
  const jid = formatJid(raw)
  const offset = Math.max(0, parseInt(req.query.offset || '0'))
  const search = (req.query.search || '').trim().toLowerCase()
  
  // Very small limits for Nokia 7210
  const limit = 3
  
  // Chat history is loaded from persistent storage on startup
  // No need to fetch from WhatsApp servers every time
  
  // Messages stored oldest→newest. For "most recent first" without O(M) copy+reverse:
  const rawMessages = chatStore.get(jid) || [];
  let allMessages, total, items;
  if (search) {
    // Search needs full scan — filter using cached lowercase text
    const searchL = search.toLowerCase();
    allMessages = [];
    for (let i = rawMessages.length - 1; i >= 0; i--) {
      const txt = getMessageSearchText(rawMessages[i]);
      if (txt.includes(searchL)) allMessages.push(rawMessages[i]);
    }
    total = allMessages.length;
    items = allMessages.slice(offset, offset + limit);
  } else {
    // No search: compute reverse window directly — O(limit) instead of O(M)
    total = rawMessages.length;
    const revStart = total - 1 - offset;
    const revEnd = Math.max(-1, revStart - limit);
    items = [];
    for (let i = revStart; i > revEnd && i >= 0; i--) {
      items.push(rawMessages[i]);
    }
  }
  
  const contact = contactStore.get(jid)
  const chatName = contact?.name || contact?.notify || contact?.verifiedName || jidFriendly(jid)
  const number = jidFriendly(jid)
  const isGroup = jid.endsWith('@g.us')
  
  // Simple escaping for Nokia 7210
  const esc = text => (text || '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
  
  // Simple truncate
  const truncate = (text, maxLength) => {
    if (!text) return ''
    if (text.length <= maxLength) return text
    return text.substring(0, maxLength - 3) + '...'
  }
  
  // Simple timestamp for Nokia
  const formatTime = (timestamp) => {
    const date = new Date(Number(timestamp) * 1000)
    if (isNaN(date.getTime())) return ''

    const day = date.getDate().toString().padStart(2, '0')
    const month = (date.getMonth() + 1).toString().padStart(2, '0')
    const year = date.getFullYear()
    const hours = date.getHours().toString().padStart(2, '0')
    const mins = date.getMinutes().toString().padStart(2, '0')
    const secs = date.getSeconds().toString().padStart(2, '0')

    return `${day}/${month}/${year} ${hours}:${mins}:${secs}`
  }
  
  let messageList = ''
  
  if (items.length === 0) {
    messageList = '<p>No messages</p>'
  } else {
    messageList = items.map((m, idx) => {
      const who = m.key.fromMe ? 'Me' : (chatName.length > 10 ? chatName.substring(0, 10) : chatName)
      const time = formatTime(m.messageTimestamp)
      const msgNumber = idx + 1
      const mid = m.key.id
      
      // Handle different message types for Nokia
      let text = ''
      let mediaLink = ''
      
      if (m.message) {
        if (m.message.imageMessage) {
          const img = m.message.imageMessage
          const size = Math.round((img.fileLength || 0) / 1024)
          text = `[IMG ${size}KB]`
          if (img.caption) text += ` ${truncate(img.caption, 30)}`
          mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}">[View IMG]</a>`
          
        } else if (m.message.videoMessage) {
          const vid = m.message.videoMessage
          const size = Math.round((vid.fileLength || 0) / 1024)
          text = `[VID ${size}KB]`
          if (vid.caption) text += ` ${truncate(vid.caption, 30)}`
          mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}">[View VID]</a>`
          
        } else if (m.message.audioMessage) {
          const aud = m.message.audioMessage
          const size = Math.round((aud.fileLength || 0) / 1024)
          const duration = aud.seconds || 0
          text = `[AUD ${size}KB ${duration}s]`
          // Show transcription preview if available
          if (m.transcription && m.transcription !== '[Trascrizione fallita]' && m.transcription !== '[Audio troppo lungo per la trascrizione]') {
            text += `<br/><small>${truncate(m.transcription, 60)}</small>`
          }
          mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}">[View AUD]</a>` +
            ` <a href="/wml/media/${encodeURIComponent(mid)}.mp3">[MP3]</a>` +
            ` <a href="/wml/media/${encodeURIComponent(mid)}.amr">[AMR]</a>`
          
        } else if (m.message.documentMessage) {
          const doc = m.message.documentMessage
          const size = Math.round((doc.fileLength || 0) / 1024)
          const filename = doc.fileName || 'file'
          text = `[DOC ${size}KB] ${truncate(filename, 20)}`
          mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}">[View DOC]</a>`
          
        } else if (m.message.stickerMessage) {
          text = '[STICKER]'
          mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}">[View STK]</a>`
          
        } else {
          text = truncate(messageText(m) || '', 50)
        }
      } else {
        text = truncate(messageText(m) || '', 50)
      }
      
      return `<p>${msgNumber}. ${esc(who)} (${time})<br/>${esc(text)}${mediaLink}</p>`
    }).join('')
  }
  
  // Simple navigation for Nokia
  const olderOffset = offset + limit
  const olderLink = olderOffset < total ? 
    `<p><a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}&amp;offset=${olderOffset}&amp;search=${encodeURIComponent(search)}" accesskey="2">2-Older</a></p>` : ''
  
  const newerOffset = Math.max(0, offset - limit)
  const newerLink = offset > 0 ? 
    `<p><a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}&amp;offset=${newerOffset}&amp;search=${encodeURIComponent(search)}" accesskey="3">3-Newer</a></p>` : ''
  
  // Simple search for Nokia
  const searchBox = search ? 
    `<p>Search: ${esc(search)}</p><p><a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}">Clear</a></p>` : 
    `<p><a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}&amp;search=prompt">Search</a></p>`
  
  const body = `<p>${esc(chatName.length > 15 ? chatName.substring(0, 15) : chatName)}</p>
<p>Msgs ${offset + 1}-${Math.min(offset + limit, total)}/${total}</p>
${searchBox}
${messageList}
${newerLink}
${olderLink}
<p><a href="/wml/send.text.wml?to=${encodeURIComponent(jid)}" accesskey="1">1-Send</a></p>
<p><a href="/wml/chats.wml" accesskey="0">0-Back</a></p>`
  
  // Nokia 7210 compatible WML 1.1
  const wmlOutput = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
<head><meta http-equiv="Cache-Control" content="no-cache, no-store"/></head>
<card id="chat" title="Chat">
${body}
</card>
</wml>`
  
  // Nokia 7210 headers
  res.setHeader('Content-Type', 'text/vnd.wap.wml; charset=iso-8859-1')
  res.setHeader('Cache-Control', 'no-cache')
  res.setHeader('Pragma', 'no-cache')
  
  const encodedBuffer = iconv.encode(wmlOutput, 'iso-8859-1')
  res.send(encodedBuffer)
})*/

app.get("/wml/chat.wml", async (req, res) => {
  const userAgent = req.headers["user-agent"] || "";
  const isOldNokia = true;

  const raw = req.query.jid || "";
  const jid = formatJid(raw);
  // Reset per-chat unread count when user opens the chat
  if (jid) {
    perChatUnreadCount.set(jid, 0);
    if (cachedUnreadCount >= 0) cachedUnreadCount = -1;
  }
  const offset = Math.max(0, parseInt(req.query.offset || "0"));
  const search = (req.query.search || "").trim().toLowerCase();

  // Fixed limit to 3 elements per page
  const limit = 3;

  // Chat history is loaded from persistent storage on startup
  // Messages are already sorted when saved (most recent last)
  const allMessages = chatStore.get(jid) || [];

  // OPTIMIZATION: Filter first, then slice (avoid processing all messages)
  let filteredMessages = allMessages;
  if (search) {
    filteredMessages = allMessages.filter((m) =>
      (messageText(m) || "").toLowerCase().includes(search)
    );
  }

  const totalMessages = filteredMessages.length;

  // OPTIMIZATION: Get last N messages directly (reverse order for display)
  // Messages are stored oldest->newest, we want to show newest->oldest
  const startIdx = Math.max(0, totalMessages - offset - limit);
  const endIdx = totalMessages - offset;
  const items = filteredMessages.slice(startIdx, endIdx).reverse();

  // OPTIMIZATION: Use cached contact name (no await, no API call)
  const contact = contactStore.get(jid);
  const chatName = contact?.name || contact?.notify || jidFriendly(jid);
  const number = jidFriendly(jid);
  const isGroup = jid.endsWith("@g.us");

  // Enhanced escaping that works for both Nokia and modern devices
  // Uses global escWml — single-pass O(L) instead of O(5L)

  // Truncation function
  const truncate = (text, maxLength) => {
    if (!text) return "";
    if (text.length <= maxLength) return text;
    return text.substring(0, maxLength - 3) + "...";
  };

  // Enhanced timestamp formatting with date and time
  const formatMessageTimestamp = (timestamp) => {
    const date = new Date(Number(timestamp) * 1000);
    if (isNaN(date.getTime())) return "Invalid date";

    if (isOldNokia) {
      // Simple format for Nokia: dd/mm/yyyy hh:mm:ss
      const day = date.getDate().toString().padStart(2, "0");
      const month = (date.getMonth() + 1).toString().padStart(2, "0");
      const year = date.getFullYear();
      const hours = date.getHours().toString().padStart(2, "0");
      const mins = date.getMinutes().toString().padStart(2, "0");
      const secs = date.getSeconds().toString().padStart(2, "0");
      return `${day}/${month}/${year} ${hours}:${mins}:${secs}`;
    } else {
      // Full format for modern devices: 30 Dec 2024 14:30:45
      const timeStr = date.toLocaleTimeString("en-GB", {
        hour: "2-digit",
        minute: "2-digit",
        second: "2-digit",
      });
      const dateStr = date.toLocaleDateString("en-GB", {
        day: "2-digit",
        month: "short",
        year: "numeric",
      });
      return `${dateStr} ${timeStr}`;
    }
  };

  // Message list with full media support
  let messageList = "";

  if (items.length === 0) {
    messageList = "<p>No messages</p>";
  } else {
    messageList = items
      .map((m, idx) => {
        // For group messages, show sender name and number
        let who = "Unknown";
        if (m.key.fromMe) {
          who = "Me";
        } else if (isGroup) {
          // Get participant JID (sender in group)
          const participantJid = m.key.participant || m.key.participantAlt;
          if (participantJid) {
            // Get contact name from store
            const participantContact = contactStore.get(participantJid);
            const senderName = participantContact?.name || m.pushName || "Unknown";
            const senderNumber = jidFriendly(participantJid);

            // Show name + number for groups
            who = isOldNokia
              ? `${senderName.substring(0, 10)} (${senderNumber.substring(0, 10)})`
              : `${senderName} (${senderNumber})`;
          } else {
            who = m.pushName || "Unknown";
          }
        } else {
          // Direct chat - use chat name
          who = isOldNokia && chatName.length > 10
            ? chatName.substring(0, 10)
            : chatName;
        }
        const time = formatMessageTimestamp(m.messageTimestamp);
        const msgNumber = idx + 1; // 1 = most recent
        const mid = m.key.id;

        // Handle different message types with full media support
        let text = "";
        let mediaLink = "";

        if (m.message) {
          if (m.message.imageMessage) {
            const img = m.message.imageMessage;
            const size = Math.round((img.fileLength || 0) / 1024);
            text = isOldNokia ? `[IMG ${size}KB]` : `[IMAGE ${size}KB]`;
            if (img.caption)
              text += ` ${truncate(img.caption, isOldNokia ? 30 : 50)}`;

            if (isOldNokia) {
              mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(
                mid
              )}&amp;jid=${encodeURIComponent(jid)}">[View IMG]</a>`;
            } else {
              mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(
                mid
              )}&amp;jid=${encodeURIComponent(
                jid
              )}">[View Image]</a> | <a href="/wml/media/${encodeURIComponent(
                mid
              )}.jpg">[Download]</a>`;
            }
          } else if (m.message.videoMessage) {
            const vid = m.message.videoMessage;
            const size = Math.round((vid.fileLength || 0) / 1024);
            const duration = vid.seconds || 0;
            text = isOldNokia
              ? `[VID ${size}KB]`
              : `[VIDEO ${size}KB, ${duration}s]`;
            if (vid.caption)
              text += ` ${truncate(vid.caption, isOldNokia ? 30 : 50)}`;

            if (isOldNokia) {
              mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(
                mid
              )}&amp;jid=${encodeURIComponent(jid)}">[View VID]</a>`;
            } else {
              mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(
                mid
              )}&amp;jid=${encodeURIComponent(
                jid
              )}">[View Video]</a> | <a href="/wml/media/${encodeURIComponent(
                mid
              )}.mp4">[Download]</a>`;
            }
          } // Nel blocco che genera la lista dei messaggi, sostituisci la gestione degli audio con questo:
          else if (m.message.audioMessage) {
            const aud = m.message.audioMessage;
            const size = Math.round((aud.fileLength || 0) / 1024);
            const duration = aud.seconds || 0;
            text = `[AUDIO ${size}KB ${duration}s]`;

            // Aggiungi il link per la trascrizione se disponibile
            if (
              m &&
              m.transcription &&
              m.transcription !== "[Trascrizione fallita]" &&
              m.transcription !== "[Audio troppo lungo per la trascrizione]"
            ) {
              mediaLink = `<br/>
 
      <a href="/wml/audio-transcription.wml?mid=${encodeURIComponent(
        mid
      )}&amp;jid=${encodeURIComponent(jid)}">[View Transcription]</a>`;
            }
          } else if (m.message.documentMessage) {
            const doc = m.message.documentMessage;
            const size = Math.round((doc.fileLength || 0) / 1024);
            const filename = doc.fileName || "file";
            text = isOldNokia
              ? `[DOC ${size}KB] ${truncate(filename, 20)}`
              : `[DOCUMENT ${size}KB] ${truncate(filename, 40)}`;

            const ext = filename.split(".").pop() || "bin";
            if (isOldNokia) {
              mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(
                mid
              )}&amp;jid=${encodeURIComponent(jid)}">[View DOC]</a>`;
            } else {
              mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(
                mid
              )}&amp;jid=${encodeURIComponent(
                jid
              )}">[View Document]</a> | <a href="/wml/media/${encodeURIComponent(
                mid
              )}.${ext}">[Download]</a>`;
            }
          } else if (m.message.stickerMessage) {
            const sticker = m.message.stickerMessage;
            const content = extractMessageContent(m.message);
            const inlineText = extractInlineTextFromContent(content);
            const stickerHuman = stickerTextWithOptionalText(sticker, inlineText, false);
            const stickerShort = stickerTextWithOptionalText(sticker, inlineText, true);
            const dirTag = m.key?.fromMe ? "[out]" : "[in]";
            text = isOldNokia ? `${dirTag} ${stickerShort}` : `${dirTag} ${stickerHuman}`;

            if (isOldNokia) {
              mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(
                mid
              )}&amp;jid=${encodeURIComponent(jid)}">[View STK]</a> <a href="/wml/media/${encodeURIComponent(
                mid
              )}.wbmp">[WBMP]</a><br/><img src="/wml/media/${encodeURIComponent(
                mid
              )}.wbmp" alt="STK"/>`;
            } else {
              const gifLink = sticker.isAnimated
                ? ` | <a href="/wml/media/${encodeURIComponent(mid)}.gif">[GIF]</a>`
                : "";
              mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(
                mid
              )}&amp;jid=${encodeURIComponent(
                jid
              )}">[View Sticker]</a> | <a href="/wml/media/${encodeURIComponent(
                mid
              )}.jpg">[JPG]</a> | <a href="/wml/media/${encodeURIComponent(
                mid
              )}.wbmp">[WBMP]</a>${gifLink}<br/><img src="/wml/media/${encodeURIComponent(
                mid
              )}.jpg" alt="Sticker"/>`;
            }
          } else {
            text = truncate(messageText(m) || "", isOldNokia ? 50 : 100);
          }
        } else {
          text = truncate(messageText(m) || "", isOldNokia ? 50 : 100);
        }

        // Format message entry
        if (isOldNokia) {
          const dir = m.key.fromMe ? "[out]" : "[in]";
          const shortWho = who.length > 9 ? who.substring(0, 8) + "." : who;
          return `<p>${dir} ${time} <b>${escWml(shortWho)}</b><br/>${escWml(text)}${mediaLink}</p>`;
        } else {
          const typeIndicator = m.key.fromMe ? "[out]" : "[in]";
          const isVeryRecent = idx < 3;
          const recentIndicator = isVeryRecent ? "[NEW] " : "";

          return `<p>${recentIndicator}<b>${msgNumber}. ${typeIndicator} ${escWml(
            who
          )}</b><br/>
          <small><b>Time:</b> ${time}</small><br/>
          <small><b>Message:</b> ${escWml(text)}</small>${mediaLink}<br/>
          <a href="/wml/msg.wml?mid=${encodeURIComponent(
            mid
          )}&amp;jid=${encodeURIComponent(jid)}">[Details]</a> 
          <a href="/wml/send.text.wml?to=${encodeURIComponent(
            jid
          )}&amp;reply=${encodeURIComponent(mid)}">[Reply]</a>
        </p>`;
        }
      })
      .join("");
  }

  // Enhanced navigation with First/Last buttons
  const totalPages = Math.ceil(totalMessages / limit);
  const currentPage = Math.floor(offset / limit) + 1;

  // Calculate navigation offsets
  const firstOffset = 0;
  const lastOffset = Math.max(0, (totalPages - 1) * limit);
  const olderOffset = offset + limit;
  const newerOffset = Math.max(0, offset - limit);

  // Build navigation links
  let navigationLinks = [];

  // First button (only if not on first page)
  if (offset > 0) {
    const firstLink = isOldNokia
      ? `<a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}&amp;offset=${firstOffset}&amp;search=${encodeURIComponent(
          search
        )}" accesskey="7">[7]Top</a>`
      : `<a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}&amp;offset=${firstOffset}&amp;search=${encodeURIComponent(
          search
        )}" accesskey="7">[7] First</a>`;
    navigationLinks.push(firstLink);
  }

  // Newer/Previous button
  if (offset > 0) {
    const newerLink = isOldNokia
      ? `<a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}&amp;offset=${newerOffset}&amp;search=${encodeURIComponent(
          search
        )}" accesskey="3">[3]&lt;&lt;</a>`
      : `<a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}&amp;offset=${newerOffset}&amp;search=${encodeURIComponent(
          search
        )}" accesskey="3">[3] Newer</a>`;
    navigationLinks.push(newerLink);
  }

  // Older/Next button
  if (olderOffset < totalMessages) {
    const olderLink = isOldNokia
      ? `<a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}&amp;offset=${olderOffset}&amp;search=${encodeURIComponent(
          search
        )}" accesskey="2">[2]&gt;&gt;</a>`
      : `<a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}&amp;offset=${olderOffset}&amp;search=${encodeURIComponent(
          search
        )}" accesskey="2">[2] Older</a>`;
    navigationLinks.push(olderLink);
  }

  // Last button (only if not on last page)
  if (offset < lastOffset) {
    const lastLink = isOldNokia
      ? `<a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}&amp;offset=${lastOffset}&amp;search=${encodeURIComponent(
          search
        )}" accesskey="8">[8]Bot</a>`
      : `<a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}&amp;offset=${lastOffset}&amp;search=${encodeURIComponent(
          search
        )}" accesskey="8">[8] Last</a>`;
    navigationLinks.push(lastLink);
  }

  // Numeri di pagina (max 5 visibili: due prima, attuale, due dopo)
  let pageNumbers = "";
  const startPage = Math.max(1, currentPage - 2);
  const endPage = Math.min(totalPages, currentPage + 2);

  for (let p = startPage; p <= endPage; p++) {
    if (p === currentPage) {
      pageNumbers += `<b>[${p}]</b> `;
    } else {
      const offsetForPage = (p - 1) * limit;
      pageNumbers += `<a href="/wml/chat.wml?jid=${encodeURIComponent(
        jid
      )}&amp;offset=${offsetForPage}&amp;search=${encodeURIComponent(
        search
      )}">${p}</a> `;
    }
  }

  // Bottoni First/Last e Prev/Next
  const firstPage =
    currentPage > 1
      ? `<a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}&amp;offset=0&amp;search=${encodeURIComponent(search)}">[First]</a>`
      : "";

  const prevPage =
    currentPage > 1
      ? `<a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}&amp;offset=${newerOffset}&amp;search=${encodeURIComponent(
          search
        )}">[Previous]</a>`
      : "";

  const nextPage =
    currentPage < totalPages
      ? `<a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}&amp;offset=${olderOffset}&amp;search=${encodeURIComponent(
          search
        )}">[Next]</a>`
      : "";

  const lastPage =
    currentPage < totalPages
      ? `<a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}&amp;offset=${lastOffset}&amp;search=${encodeURIComponent(
          search
        )}">[Last]</a>`
      : "";

  // Sezione completa di navigazione
  const navigationSection = `
  <p>
    ${firstPage} ${firstPage && prevPage ? "" : ""} ${prevPage}
    ${pageNumbers}
    ${nextPage} ${nextPage && lastPage ? "" : ""} ${lastPage}
  </p>`;

  // Search form adapted to device capability
  const searchForm = isOldNokia
    ? search
      ? `<p>Search: ${escWml(
          search
        )}</p><p><a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}">Clear</a></p>`
      : `<p><a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}&amp;search=prompt">Search</a></p>`
    : `<p><b>Search Messages:</b></p>
     <p>
       <input name="searchQuery" title="Search..." value="${escWml(
         search
       )}" size="15" maxlength="50"/>
     </p>
     <p>
       <anchor title="Search">Search
         <go href="/wml/chat.wml" method="get">
           <postfield name="jid" value="${escWml(jid)}"/>
           <postfield name="search" value="$(searchQuery)"/>
           <postfield name="offset" value="0"/>
         </go>
       </anchor>
     </p>
     <do type="accept" label="${t('common.search')}">
       <go href="/wml/chat.wml" method="get">
         <postfield name="jid" value="${escWml(jid)}"/>
         <postfield name="search" value="$(searchQuery)"/>
         <postfield name="offset" value="0"/>
       </go>
     </do>
     ${
       search
         ? `<p>Searching: <b>${escWml(
             search
           )}</b> | <a href="/wml/chat.wml?jid=${encodeURIComponent(
             jid
           )}">[Clear]</a></p>`
         : ""
     }`;

  // Page info adapted to device
  const pageInfo = isOldNokia
    ? `<p>Pg ${currentPage}/${totalPages} | ${totalMessages} msg</p>`
    : `<p><b>Page ${currentPage} of ${totalPages}</b></p>
     <p><b>Messages ${offset + 1}-${Math.min(
        offset + limit,
        totalMessages
      )} of ${totalMessages}</b></p>
     <p>Showing 5 messages per page (most recent first)</p>`;

  // Quick actions adapted to device
  const favoriteLink = isFavorite(jid)
    ? `<a href="/wml/favorites-remove.wml?jid=${encodeURIComponent(jid)}&amp;back=chat" accesskey="5">${isOldNokia ? '5-Unfav' : '[5] Remove Favorite'}</a>`
    : `<a href="/wml/favorites-add.wml?jid=${encodeURIComponent(jid)}&amp;back=chat" accesskey="5">${isOldNokia ? '5-Fav' : '[5] Add to Favorites'}</a>`;

  const quickActions = isOldNokia
    ? `<p><a href="/wml/send-quick.wml?to=${encodeURIComponent(
        jid
      )}" accesskey="1">[1]Send</a> <a href="/wml/send.sticker.wml?to=${encodeURIComponent(
        jid
      )}" accesskey="3">[3]Stk</a> <a href="/wml/chats.wml" accesskey="0">[0]Back</a></p>
     <p><a href="/opera/send?jid=${encodeURIComponent(jid)}" accesskey="4">[4]File</a> ${favoriteLink}</p>`
    : `<p><b>Quick Actions:</b></p>
     <p>
       <a href="/wml/send-quick.wml?to=${encodeURIComponent(
         jid
       )}" accesskey="1">[1] Send Message</a>
       <a href="/opera/send?jid=${encodeURIComponent(
         jid
       )}" accesskey="2">[2] Send File</a>
       <a href="/wml/send.sticker.wml?to=${encodeURIComponent(
         jid
       )}" accesskey="3">[3] Send Sticker</a>
       <a href="/wml/contact.wml?jid=${encodeURIComponent(
         jid
       )}" accesskey="4">[4] Contact Info</a>
       ${
         number && !isGroup
           ? ` | <a href="wtai://wp/mc;${number}" accesskey="9">[9] Call</a>`
           : ""
       }
       ${
         number && !isGroup
           ? ` | <a href="wtai://wp/ms;${number};">[SMS]</a>`
           : ""
       }
       <br/>
       ${favoriteLink}
     </p>
     <p>
       <a href="/wml/chats.wml" accesskey="0">[0] Back to Chats</a> |
       <a href="/wml/home.wml" accesskey="*">[*] Home</a>
     </p>`;

  // Build final body
  const chatTitle = isOldNokia
    ? chatName.length > 15
      ? chatName.substring(0, 15)
      : chatName
    : chatName;
  const refreshNonce = Date.now();
  const timerVarName = "rtv";
  const timerVarRef = `$(${timerVarName})`;
  const autoRefreshTarget = `/wml/chat.wml?jid=${encodeURIComponent(jid)}&amp;offset=0&amp;search=${encodeURIComponent(search)}&amp;_rt=${refreshNonce}&amp;_rv=${timerVarRef}`;
  const manualRefreshTarget = `/wml/chat.wml?jid=${encodeURIComponent(jid)}&amp;offset=${offset}&amp;search=${encodeURIComponent(search)}&amp;_rt=${refreshNonce}&amp;_rv=${timerVarRef}`;

  const body = isOldNokia
    ? `<p><b>${escWml(chatTitle)}</b></p>
${pageInfo}
${messageList}
${navigationSection}
${quickActions}`
    : `<p><b>${escWml(chatTitle)}</b> ${isGroup ? "[GROUP]" : "[CHAT]"}</p>
<p>${escWml(number)} | Total: ${totalMessages} messages</p>
${searchForm}
${pageInfo}
${messageList}
${navigationSection}
${quickActions}`;

  // Create WML output with appropriate DOCTYPE
  const wmlOutput = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
<head><meta http-equiv="Cache-Control" content="no-cache, no-store"/></head>
<card id="chat" title="Chat" ontimer="${autoRefreshTarget}">
<onevent type="onenterforward"><refresh><setvar name="${timerVarName}" value="${refreshNonce}"/></refresh></onevent>
<onevent type="ontimer"><go href="${autoRefreshTarget}"/></onevent>
<timer value="${getWmlRefreshTimerUnits()}"/>
${body}
<do type="accept" label="${t('common.send')}">
  <go href="/wml/send-quick.wml?to=${encodeURIComponent(jid)}"/>
</do>
<do type="options" label="${t('common.refresh')}">
  <go href="${manualRefreshTarget}"/>
</do>
</card>
</wml>`;

  sendRawWmlAware(res, wmlOutput);
});
// Route per visualizzare info media - WAP friendly come QR

function encodeMultiByte(value) {
  if (value < 128) {
    return Buffer.from([value]);
  }

  const bytes = [];
  let remaining = value;

  // Encoding multi-byte WBMP standard
  while (remaining >= 128) {
    bytes.unshift(remaining & 0x7f);
    remaining = remaining >> 7;
  }
  bytes.unshift(remaining | 0x80);

  return Buffer.from(bytes);
}

function createWBMP(pixels, width, height) {
  // Header WBMP standard
  const typeField = Buffer.from([0x00]);
  const fixHeader = Buffer.from([0x00]);
  const widthBytes = encodeMultiByte(width);
  const heightBytes = encodeMultiByte(height);

  // Calcola dimensioni data
  const bytesPerRow = Math.ceil(width / 8);
  const dataSize = bytesPerRow * height;
  const data = Buffer.alloc(dataSize, 0x00); // Inizializza a 0 (bianco)

  // Converte pixel in 1-bit
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const pixelIndex = y * width + x;
      const grayscale = pixels[pixelIndex]; // Già grayscale

      // WBMP: 1 = nero, 0 = bianco
      const isBlack = grayscale < 128;

      if (isBlack) {
        const byteIndex = y * bytesPerRow + Math.floor(x / 8);
        const bitPosition = 7 - (x % 8);
        data[byteIndex] |= 1 << bitPosition;
      }
    }
  }

  return Buffer.concat([typeField, fixHeader, widthBytes, heightBytes, data]);
}

app.get("/wml/audio-transcription.wml", async (req, res) => {
  try {
    const mid = req.query.mid || "";
    const jid = req.query.jid || "";

    // O(1) lookup via messageStore instead of O(n) .find()
    const targetMessage = messageStore.get(mid) || null;

    if (!targetMessage) {
      sendWml(
        res,
        resultCard(
          t('common.error'),
          [t('audio.msg_not_found')],
          `/wml/chat.wml?jid=${encodeURIComponent(jid)}&limit=3`
        )
      );
      return;
    }

    // Verifica che sia un messaggio audio
    if (!targetMessage.message?.audioMessage) {
      sendWml(
        res,
        resultCard(
          t('common.error'),
          [t('audio.not_audio_msg')],
          `/wml/chat.wml?jid=${encodeURIComponent(jid)}&limit=3`
        )
      );
      return;
    }

    const contact = contactStore.get(jid);
    const chatName = contact?.name || contact?.notify || jidFriendly(jid);
    const aud = targetMessage.message.audioMessage;
    const duration = aud.seconds || 0;
    const size = Math.round((aud.fileLength || 0) / 1024);

    // Prepara la trascrizione
    let transcriptionText = "";
    let transcriptionStatus = "";

    if (targetMessage.transcription) {
      if (targetMessage.transcription === "[Trascrizione fallita]") {
        transcriptionStatus = t('audio.failed');
        transcriptionText = t('audio.failed_msg');
      } else if (
        targetMessage.transcription ===
        "[Audio troppo lungo per la trascrizione]"
      ) {
        transcriptionStatus = t('audio.too_long');
        transcriptionText = t('audio.too_long_msg');
      } else {
        transcriptionStatus = t('audio.complete');
        transcriptionText = targetMessage.transcription;
      }
    } else {
      transcriptionStatus = t('audio.processing');
      transcriptionText = t('audio.in_progress');
    }

    const body = `
      <p><b>${t('audio.message_title')}</b></p>

      <p><b>${t('audio.from')}</b> ${esc(chatName)}</p>
      <p><b>${t('audio.duration')}</b> ${duration} ${t('audio.seconds')}</p>
      <p><b>${t('audio.size')}</b> ${size}KB</p>
      <p><b>${t('audio.status')}</b> ${transcriptionStatus}</p>

      <p><b>${t('audio.transcription')}</b></p>
      <p>${esc(transcriptionText)}</p>

      <p><b>${t('common.actions')}</b></p>
      <p>
        <a href="/wml/media/${encodeURIComponent(mid)}.amr" accesskey="1">[1] AMR (7250i)</a><br/>
        <a href="/wml/media/${encodeURIComponent(mid)}.mp3" accesskey="2">[2] MP3 (N70)</a><br/>
        <a href="/wml/media/${encodeURIComponent(mid)}.3gp" accesskey="3">[3] 3GP (N70)</a><br/>
        <a href="/wml/media/${encodeURIComponent(mid)}.m4a" accesskey="4">[4] M4A/AAC</a><br/>
        <a href="/wml/stream/audio/${encodeURIComponent(mid)}.ram?format=amr" accesskey="5">[5] RealPlayer AMR</a><br/>
        <a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}&amp;limit=3" accesskey="0">${t('audio.back_to_chat')}</a>
      </p>

      <do type="accept" label="${t('audio.listen')}">
        <go href="/wml/media/${encodeURIComponent(mid)}.wav"/>
      </do>
      <do type="options" label="${t('audio.back')}">
        <go href="/wml/chat.wml?jid=${encodeURIComponent(jid)}&amp;limit=3"/>
      </do>
    `;

    sendWml(res, card("audio-transcription", t('audio.title'), body));
  } catch (error) {
    logger.error("Audio transcription page error:", error);
    sendWml(
      res,
      resultCard(
        t('audio.error'),
        [error.message || t('audio.error_loading')],
        "/wml/home.wml"
      )
    );
  }
});

app.get("/wml/media/:filename", async (req, res) => {
  try {
    const filename = req.params.filename;
    const messageId = filename.split(".")[0];
    const forceWbmp = filename.endsWith(".wbmp");
    let forceGif = filename.endsWith(".gif");
    const forceOriginal = filename.endsWith(".original.jpg");

    // Debug logging
    console.log(`Richiesta media: ${filename}, WBMP: ${forceWbmp}, GIF: ${forceGif}, Original: ${forceOriginal}`);

    // O(1) lookup via messageStore instead of O(C*M) nested loop
    const decodedId = decodeURIComponent(messageId);
    const targetMessage = messageStore.get(decodedId) || null;

    if (!sock) {
      console.log("WhatsApp disconnesso - impossibile scaricare media");
      res.status(503).send("WhatsApp disconnesso");
      return;
    }

    if (!targetMessage) {
      console.log("Messaggio non trovato");
      res.status(404).send("Media not found");
      return;
    }

    // Download media
    let mediaData = null;
    let mimeType = "application/octet-stream";
    let filename_out = filename;
    let isImage = false;

    if (targetMessage.message?.imageMessage) {
      mediaData = await downloadMediaMessage(
        targetMessage,
        "buffer",
        {},
        {
          logger,
          reuploadRequest: sock.updateMediaMessage,
        }
      );
      if (forceOriginal) {
        // Serve at full resolution — high-quality JPEG, no size limit
        try {
          mediaData = await sharp(mediaData).jpeg({ quality: 95 }).toBuffer();
        } catch (e) {
          console.error("[media] original JPEG conversion error:", e.message);
          // serve raw buffer as-is
        }
        mimeType = "image/jpeg";
        filename_out = `image_${messageId}_original.jpg`;
        isImage = false; // skip the WAP compression block; use attachment disposition
      } else {
        mimeType = forceWbmp ? "image/vnd.wap.wbmp" : "image/jpeg";
        filename_out = forceWbmp
          ? `image_${messageId}.wbmp`
          : `image_${messageId}.jpg`;
        isImage = true;
      }
    } else if (targetMessage.message?.stickerMessage) {
      mediaData = await downloadMediaMessage(
        targetMessage,
        "buffer",
        {},
        {
          logger,
          reuploadRequest: sock.updateMediaMessage,
        }
      );
      if (forceGif) {
        // Convert WebP sticker to GIF — no early return, flows through normal send path
        try {
          const meta = await sharp(mediaData, { animated: true }).metadata();
          mediaData = await sharp(mediaData, meta.pages > 1 ? { animated: true } : {})
            .gif()
            .toBuffer();
          mimeType = "image/gif";
          filename_out = `sticker_${messageId}.gif`;
          // isImage stays false — skips WBMP/JPEG processing below
        } catch (gifErr) {
          console.error("[Sticker] GIF conversion failed, falling back to JPEG:", gifErr.message);
          // Fall through to JPEG path
          mimeType = "image/jpeg";
          filename_out = `sticker_${messageId}.jpg`;
          isImage = true;
        }
      } else {
        mimeType = forceWbmp ? "image/vnd.wap.wbmp" : "image/jpeg";
        filename_out = forceWbmp
          ? `sticker_${messageId}.wbmp`
          : `sticker_${messageId}.jpg`;
        isImage = true;
      }
    } else if (targetMessage.message?.documentMessage) {
      const doc = targetMessage.message.documentMessage;
      mediaData = await downloadMediaMessage(
        targetMessage,
        "buffer",
        {},
        {
          logger,
          reuploadRequest: sock.updateMediaMessage,
        }
      );

      if (doc.mimetype && doc.mimetype.startsWith("image/")) {
        isImage = true;
        mimeType = forceWbmp ? "image/vnd.wap.wbmp" : "image/jpeg";
        filename_out = forceWbmp
          ? `doc_${messageId}.wbmp`
          : `doc_${messageId}.jpg`;
      } else {
        mimeType = doc.mimetype || "application/octet-stream";
        filename_out = doc.fileName || `document_${messageId}.bin`;
      }
    }
    // ============ VIDEO DOWNLOAD (3GP for Symbian) ============
    else if (targetMessage.message?.videoMessage) {
      const vid = targetMessage.message.videoMessage;
      const requestedFormat = filename.split('.').pop().toLowerCase();

      if (requestedFormat === '3gp') {
        // Check for pre-converted cached file first
        const cachedPath = getPreConvertedPath(messageId, '3gp');
        if (cachedPath) {
          console.log(`[Cache] Using pre-converted 3GP: ${cachedPath}`);
          mediaData = await fs.promises.readFile(cachedPath);
          mimeType = "video/3gpp";
          filename_out = `video_${messageId}.3gp`;
        } else {
          // Download and convert on-the-fly
          mediaData = await downloadMediaMessage(
            targetMessage,
            "buffer",
            {},
            {
              logger,
              reuploadRequest: sock.updateMediaMessage,
            }
          );

          console.log("Conversione video a 3GP per Symbian...");
          try {
            const tempInput = safeTempPath(`video_${messageId}_input.mp4`);
            const tempOutput = safeTempPath(`video_${messageId}_output.3gp`);

            await fs.promises.writeFile(tempInput, mediaData);

            await new Promise((resolve, reject) => {
              const ffmpegPath = ffmpeg;
              const process = spawn(ffmpegPath, [
                '-i', tempInput,
                '-y',
                '-c:v', 'h263',
                '-s', '176x144',
                '-r', '15',
                '-b:v', '64k',
                '-c:a', 'libopencore_amrnb',
                '-ar', '8000',
                '-ac', '1',
                '-b:a', '12.2k',
                tempOutput
              ]);

              let stderr = '';
              process.stderr.on('data', (data) => { stderr += data.toString(); });
              process.on('close', (code) => {
                if (code === 0) resolve();
                else reject(new Error(`FFmpeg 3GP conversion failed: ${stderr}`));
              });
            });

            mediaData = await fs.promises.readFile(tempOutput);

            // Save to in-memory + disk cache for O(1) future lookups
            cacheConvertedMedia(messageId, '3gp', tempOutput);

            // Cleanup temp files
            try {
              await fs.promises.unlink(tempInput);
              await fs.promises.unlink(tempOutput);
            } catch (e) { }

            mimeType = "video/3gpp";
            filename_out = `video_${messageId}.3gp`;
            console.log(`Video 3GP creato: ${mediaData.length} bytes`);
          } catch (convError) {
            console.error("Errore conversione 3GP:", convError);
            // Fallback: reuse already-downloaded buffer (no redundant network I/O)
            mimeType = vid.mimetype || "video/mp4";
            filename_out = `video_${messageId}.mp4`;
          }
        }
      } else {
        // Original format
        mediaData = await downloadMediaMessage(
          targetMessage,
          "buffer",
          {},
          { logger, reuploadRequest: sock.updateMediaMessage }
        );
        mimeType = vid.mimetype || "video/mp4";
        filename_out = `video_${messageId}.mp4`;
      }
    }
    // ============ AUDIO DOWNLOAD (WAV/AMR/MP3 for Symbian) ============
    else if (targetMessage.message?.audioMessage) {
      const aud = targetMessage.message.audioMessage;
      const requestedFormat = filename.split('.').pop().toLowerCase();
      const allowedAudioFormats = ['ogg', 'oga', 'wav', 'amr', 'mp3', '3gp', 'aac', 'm4a'];

      // Validate requested format to prevent unexpected paths
      if (!allowedAudioFormats.includes(requestedFormat)) {
        console.log(`Formato audio non supportato: ${requestedFormat}`);
        res.status(400).send("Unsupported audio format");
        return;
      }

      // O(1) cache check BEFORE downloading from WhatsApp — avoids wasted network I/O
      const cachedPath = (requestedFormat !== 'ogg' && requestedFormat !== 'oga') ? getPreConvertedPath(messageId, requestedFormat) : null;
      if (cachedPath) {
        try {
          console.log(`[Cache HIT] Using pre-converted ${requestedFormat}: ${cachedPath}`);
          mediaData = await fs.promises.readFile(cachedPath);
          const formatMeta = {
            wav: 'audio/wav',
            amr: 'audio/amr',
            mp3: 'audio/mpeg',
            '3gp': 'audio/3gpp',
            aac: 'audio/aac',
            m4a: 'audio/mp4'
          };
          mimeType = formatMeta[requestedFormat] || aud.mimetype || 'audio/ogg';
          filename_out = `audio_${messageId}.${requestedFormat}`;
        } catch (cacheErr) {
          console.error(`[Cache] Errore lettura cache ${cachedPath}:`, cacheErr);
          // Cache file corrupted/deleted — fall through to re-download and convert
          mediaData = null;
        }
      }

      // Download original audio from WhatsApp if not served from cache
      if (!mediaData) {
        try {
          mediaData = await downloadMediaMessage(targetMessage, "buffer", {}, { logger, reuploadRequest: sock?.updateMediaMessage });
        } catch (dlErr) {
          console.error(`Errore download audio da WhatsApp:`, dlErr);
          // Retry once with media re-upload request
          try {
            console.log(`[Audio] Retry download con reupload...`);
            const updatedMsg = await sock.updateMediaMessage(targetMessage);
            mediaData = await downloadMediaMessage(updatedMsg || targetMessage, "buffer", {}, { logger, reuploadRequest: sock?.updateMediaMessage });
          } catch (retryErr) {
            console.error(`[Audio] Retry download fallito:`, retryErr);
            mediaData = null;
          }
        }
      }

      if (!mediaData) {
        console.log("Impossibile scaricare audio da WhatsApp");
        res.status(502).send("Impossibile scaricare audio da WhatsApp. Riprova.");
        return;
      }

      if (requestedFormat === 'ogg' || requestedFormat === 'oga') {
        // Original format — already downloaded
        mimeType = aud.mimetype || "audio/ogg";
        filename_out = `audio_${messageId}.ogg`;
      } else if (!cachedPath || !filename_out) {
        // Need conversion (not served from cache)
        const codecSettings = {
          wav: ['-c:a', 'pcm_s16le', '-ar', '22050', '-ac', '1'],
          amr: ['-c:a', 'libopencore_amrnb', '-ar', '8000', '-ac', '1', '-b:a', '12.2k'],
          mp3: ['-c:a', 'libmp3lame', '-ar', '22050', '-ac', '1', '-b:a', '64k'],
          aac: ['-c:a', 'aac', '-profile:a', 'aac_low', '-ar', '24000', '-ac', '1', '-b:a', '48k'],
          m4a: ['-c:a', 'aac', '-profile:a', 'aac_low', '-ar', '24000', '-ac', '1', '-b:a', '48k', '-movflags', '+faststart'],
          '3gp': ['-c:a', 'aac', '-ar', '16000', '-ac', '1', '-b:a', '32k', '-f', '3gp'],
        };
        const formatMeta = {
          wav: 'audio/wav',
          amr: 'audio/amr',
          mp3: 'audio/mpeg',
          aac: 'audio/aac',
          m4a: 'audio/mp4',
          '3gp': 'audio/3gpp'
        };
        const codec = codecSettings[requestedFormat];

        if (codec) {
          console.log(`Conversione audio a ${requestedFormat.toUpperCase()}...`);
          try {
            const tempInput = safeTempPath(`audio_${messageId}_input.ogg`);
            const tempOutput = safeTempPath(`audio_${messageId}_output.${requestedFormat}`);

            await fs.promises.writeFile(tempInput, mediaData);

            await new Promise((resolve, reject) => {
              const proc = spawn(ffmpeg, ['-i', tempInput, '-y', ...codec, tempOutput]);
              let stderr = '';
              proc.stderr.on('data', (data) => { stderr += data.toString(); });

              // Timeout: kill FFmpeg if stuck for more than 30 seconds
              const timeout = setTimeout(() => {
                proc.kill('SIGKILL');
                reject(new Error(`FFmpeg ${requestedFormat} timeout (30s)`));
              }, 30000);

              proc.on('close', (code) => {
                clearTimeout(timeout);
                code === 0 ? resolve() : reject(new Error(`FFmpeg ${requestedFormat} failed (code ${code}): ${stderr}`));
              });
              proc.on('error', (err) => {
                clearTimeout(timeout);
                reject(err);
              });
            });

            mediaData = await fs.promises.readFile(tempOutput);

            // Cache ALL converted formats (WAV/AMR/MP3) for O(1) future hits
            cacheConvertedMedia(messageId, requestedFormat, tempOutput);

            try { await fs.promises.unlink(tempInput); } catch (e) { }
            try { await fs.promises.unlink(tempOutput); } catch (e) { }

            mimeType = formatMeta[requestedFormat];
            filename_out = `audio_${messageId}.${requestedFormat}`;
            console.log(`Audio ${requestedFormat.toUpperCase()} creato: ${mediaData.length} bytes`);
          } catch (convError) {
            console.error(`Errore conversione ${requestedFormat}:`, convError);
            // Fallback: serve original OGG instead of failing completely
            mimeType = aud.mimetype || "audio/ogg";
            filename_out = `audio_${messageId}.ogg`;
          }
        } else {
          // Unknown format — serve original
          mimeType = aud.mimetype || "audio/ogg";
          filename_out = `audio_${messageId}.ogg`;
        }
      }
    }

    if (!mediaData) {
      console.log("Impossibile scaricare il media");
      res.status(404).send("Could not download media");
      return;
    }

    console.log(
      `Media scaricato, dimensione: ${mediaData.length} bytes, isImage: ${isImage}`
    );

    // Processa le immagini
    if (isImage) {
      try {
        const maxSizeBytes = 35 * 1024; // 35KB limit

        if (forceWbmp) {
          console.log("Conversione a WBMP per dispositivi WAP...");

          // Ottieni metadata dell'immagine originale per controllo dimensioni
          const originalMetadata = await sharp(mediaData).metadata();
          console.log(
            `Immagine originale: ${originalMetadata.width}x${originalMetadata.height}`
          );

          // Calcola dimensioni ottimali per dispositivi WAP - PIÙ LARGHE
          const maxWidth = 240; // Larghezza aumentata per schermi più grandi
          const maxHeight = 280; // Altezza aumentata per massima visibilità

          let targetWidth = originalMetadata.width;
          let targetHeight = originalMetadata.height;

          // Se l'immagine è troppo grande, ridimensiona mantenendo proporzioni
          if (targetWidth > maxWidth || targetHeight > maxHeight) {
            const widthRatio = maxWidth / targetWidth;
            const heightRatio = maxHeight / targetHeight;
            const ratio = Math.min(widthRatio, heightRatio);

            targetWidth = Math.round(targetWidth * ratio);
            targetHeight = Math.round(targetHeight * ratio);
            console.log(
              `Ridimensionando a ${targetWidth}x${targetHeight} per compatibilità WAP estesa`
            );
          }

          // Processamento pre-resize per preservare i dettagli
          let processedImage = sharp(mediaData)
            .linear(1.2, -(128 * 0.2)) // Aumenta contrasto lineare
            .modulate({
              brightness: 1.05,
              saturation: 0.8,
              hue: 0,
            });

          // Applica resize solo se necessario
          if (
            targetWidth !== originalMetadata.width ||
            targetHeight !== originalMetadata.height
          ) {
            processedImage = processedImage.resize(targetWidth, targetHeight, {
              kernel: sharp.kernel.lanczos3,
              fit: "contain",
              position: "center",
              background: { r: 255, g: 255, b: 255, alpha: 1 },
            });
          }

          // Converti in grayscale con altissima qualità
          const { data: pixels, info } = await processedImage
            .greyscale()
            .linear(1.3, -30) // Contrasto aggressivo pre-normalizzazione
            .normalise({
              lower: 1, // Percentile inferiore per bianco puro
              upper: 99, // Percentile superiore per nero puro
            })
            .sharpen({
              sigma: 1.5, // Raggio sharpening
              flat: 2, // Soglia flat areas
              jagged: 3, // Soglia jagged areas
            })
            .threshold(128, {
              greyscale: true,
              grayscale: true,
            }) // Soglia ottimale per bianco/nero
            .raw()
            .toBuffer({ resolveWithObject: true });

          console.log(
            `Pixel estratti: ${pixels.length}, dimensioni finali: ${info.width}x${info.height}`
          );

          // Crea WBMP con dimensioni ottimizzate per WAP
          mediaData = createWBMP(pixels, info.width, info.height);
          console.log(
            `WBMP esteso per WAP ${info.width}x${info.height} creato, dimensione finale: ${mediaData.length} bytes`
          );
        } else {
          console.log("Conversione a JPEG...");
          let quality = 80;

          do {
            mediaData = await sharp(mediaData).jpeg({ quality }).toBuffer();

            console.log(
              `JPEG creato, dimensione: ${mediaData.length} bytes (limite: ${maxSizeBytes})`
            );

            // Se troppo grande, riduci solo la qualità
            if (mediaData.length > maxSizeBytes) {
              if (quality > 10) {
                quality = Math.max(10, quality - 10);
                console.log(`Riducendo qualità a ${quality}%`);
              } else {
                console.log(
                  `Qualità minima raggiunta (${quality}%), dimensione finale: ${mediaData.length} bytes`
                );
                break; // Cannot reduce quality further
              }
            } else {
              console.log(
                `JPEG ottimizzato con successo: ${mediaData.length} bytes`
              );
              break;
            }
          } while (mediaData.length > maxSizeBytes && quality >= 10);
        }

        // Controllo finale dimensione
        if (mediaData.length > maxSizeBytes) {
          console.log(
            `ATTENZIONE: File ancora sopra il limite: ${mediaData.length} bytes (max: ${maxSizeBytes})`
          );
        }
      } catch (conversionError) {
        console.error("Errore conversione immagine:", conversionError);
        // Continua con l'immagine originale
      }
    }

    // Controllo finale per tutti i file (anche non-immagini)
    const maxSizeBytes = 35 * 1024; // 35KB limit
    if (mediaData.length > maxSizeBytes) {
      console.log(
        `ATTENZIONE: File troppo grande: ${mediaData.length} bytes (max: ${maxSizeBytes})`
      );
      // Opzionalmente potresti ritornare un errore:
      // res.status(413).send('File too large')
      // return
    }

    // Headers
    if (forceWbmp && isImage) {
      console.log("Invio come WBMP");
      // Headers WAP semplificati
      res.setHeader("Content-Type", "image/vnd.wap.wbmp");
      res.setHeader("Content-Length", mediaData.length);
      res.setHeader("Cache-Control", "no-cache"); // Disabilita cache per debug
    } else if (isImage) {
      console.log("Invio come JPEG");
      res.setHeader("Content-Type", "image/jpeg");
      res.setHeader("Content-Length", mediaData.length);
      res.setHeader("Cache-Control", "no-cache");
    } else {
      // Use inline for image/audio types (GIF stickers, etc.), attachment for others.
      // forceOriginal downloads must be attachment so the browser saves the file.
      const dispType = !forceOriginal && (mimeType.startsWith("image/") || mimeType.startsWith("audio/"))
        ? "inline"
        : "attachment";
      console.log(`Invio come ${dispType} (${mimeType})`);
      res.setHeader("Content-Type", mimeType);
      res.setHeader("Content-Disposition", `${dispType}; filename="${filename_out}"`);
      res.setHeader("Content-Length", mediaData.length);
    }

    console.log(
      `Invio risposta: ${mediaData.length} bytes, Content-Type: ${res.getHeader(
        "Content-Type"
      )}`
    );
    res.send(mediaData);
  } catch (error) {
    console.error("Errore generale:", error);
    res.status(500).send("Internal Server Error");
  }
});
// Route esistente modificata per includere link alla pagina WBMP dedicata
app.get("/wml/media-info.wml", async (req, res) => {
  try {
    const messageId = req.query.mid || "";
    const jid = req.query.jid || "";

    // O(1) lookup via messageStore instead of O(n) .find()
    const targetMessage = messageStore.get(messageId) || null;

    const contact = contactStore.get(jid);
    const chatName = contact?.name || contact?.notify || jidFriendly(jid);

    // Simple escaping
    const esc = (text) =>
      (text || "")
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;");

    const body = targetMessage
      ? (() => {
          if (targetMessage.message?.imageMessage) {
            const img = targetMessage.message.imageMessage;
            const size = Math.round((img.fileLength || 0) / 1024);
            const caption = img.caption
              ? `<p><b>Caption:</b> ${esc(img.caption)}</p>`
              : "";

            return `<p><b>Image Message</b></p>
<p>From: ${esc(chatName)}</p>
<p>Size: ${size}KB</p>
<p>Type: ${img.mimetype || "image/jpeg"}</p>
${caption}
<p><b>View Image (WBMP):</b></p>
<p>
<a href="/wml/view-image.wml?mid=${encodeURIComponent(
              messageId
            )}&amp;jid=${encodeURIComponent(jid)}" accesskey="5">[5] View in Page</a>
</p>
<p><small>WAP only supports WBMP inline.<br/>
JPG/PNG are download-only.</small></p>
<p><b>Download Formats:</b></p>
<p>
<a href="/wml/media/${encodeURIComponent(messageId)}.jpg" accesskey="6">[6] JPG</a><br/>
<a href="/wml/media/${encodeURIComponent(messageId)}.original.jpg" accesskey="7">[7] Orig JPG</a><br/>
<a href="/wml/media/${encodeURIComponent(messageId)}.wbmp" accesskey="8">[8] WBMP</a>
</p>
`;
          } else if (targetMessage.message?.videoMessage) {
            const vid = targetMessage.message.videoMessage;
            const size = Math.round((vid.fileLength || 0) / 1024);
            const duration = vid.seconds || 0;
            const caption = vid.caption
              ? `<p><b>Caption:</b> ${esc(vid.caption)}</p>`
              : "";

            return `<p><b>Video Message</b></p>
<p>From: ${esc(chatName)}</p>
<p>Size: ${size}KB | Duration: ${duration}s</p>
<p>Type: ${vid.mimetype || "video/mp4"}</p>
${caption}
<p><b>WAP Playback (WBMP):</b></p>
<p>
<a href="/wml/view-video.wml?mid=${encodeURIComponent(
              messageId
            )}&amp;jid=${encodeURIComponent(jid)}" accesskey="5">[5] Play Frame-by-Frame (1 FPS)</a>
</p>
<p><small>Displays WBMP frames inline.<br/>
Press [7]/[8] to download JPG/PNG.</small></p>
<p><b>RealPlayer Stream (Video+Audio):</b></p>
<p>
<a href="/wml/stream/video/${encodeURIComponent(messageId)}.ram?format=3gp" accesskey="6">[6] 3GP Stream</a> |
<a href="/wml/stream/video/${encodeURIComponent(messageId)}.ram?format=mp4">[MP4]</a>
</p>
<p><b>Download Video:</b></p>
<p>
<a href="/wml/media/${encodeURIComponent(messageId)}.3gp" accesskey="7">[7] 3GP Mobile</a><br/>
<a href="/wml/media/${encodeURIComponent(messageId)}.original.mp4" accesskey="8">[8] MP4 Original</a>
</p>`;
          } // Nel blocco che gestisce i messaggi audio, aggiungi questo:
          else if (targetMessage.message?.audioMessage) {
            const aud = targetMessage.message.audioMessage;
            const size = Math.round((aud.fileLength || 0) / 1024);
            const duration = aud.seconds || 0;

            return `<p><b>Audio Message</b></p>
    <p>From: ${esc(chatName)}</p>
    <p>Size: ${size}KB | Duration: ${duration}s</p>
    <p>Type: ${aud.mimetype || "audio/ogg"}</p>

    ${
      targetMessage.transcription &&
      targetMessage.transcription !== "[Trascrizione fallita]" &&
      targetMessage.transcription !== "[Audio troppo lungo per la trascrizione]"
        ? `<p><b>${t('audio.transcription_available')}</b></p>
      <p><a href="/wml/audio-transcription.wml?mid=${encodeURIComponent(
        messageId
      )}&amp;jid=${encodeURIComponent(
            jid
          )}" accesskey="4">[4] View Transcription</a></p>`
        : ""
    }

    <p><b>RealPlayer Stream:</b></p>
    <p>
      <a href="/wml/stream/audio/${encodeURIComponent(
        messageId
      )}.ram?format=amr" accesskey="5">[5] AMR</a> |
      <a href="/wml/stream/audio/${encodeURIComponent(
        messageId
      )}.ram?format=mp3">[MP3]</a>
    </p>
    <p><b>Download Symbian:</b></p>
    <p>
      <a href="/wml/media/${encodeURIComponent(
        messageId
      )}.wav" accesskey="6">[6] WAV</a> |
      <a href="/wml/media/${encodeURIComponent(
        messageId
      )}.amr" accesskey="7">[7] AMR</a> |
      <a href="/wml/media/${encodeURIComponent(
        messageId
      )}.mp3" accesskey="8">[8] MP3</a>
    </p>
    <p><b>Original:</b></p>
    <p>
      <a href="/wml/media/${encodeURIComponent(
        messageId
      )}.ogg" accesskey="9">[9] OGG</a>
    </p>`;
          } else if (targetMessage.message?.documentMessage) {
            const doc = targetMessage.message.documentMessage;
            const size = Math.round((doc.fileLength || 0) / 1024);
            const filename = doc.fileName || "document";
            const ext = filename.split(".").pop() || "bin";

            return `<p><b>Document</b></p>
<p>From: ${esc(chatName)}</p>
<p>Name: ${esc(filename)}</p>
<p>Size: ${size}KB</p>
<p>Type: ${doc.mimetype || "unknown"}</p>
<p><b>Download Options:</b></p>
<p>
<a href="/wml/media/${encodeURIComponent(messageId)}.${ext}">[Original]</a> 
<a href="/wml/media-text/${encodeURIComponent(messageId)}">[Text View]</a>
</p>`;
          } else if (targetMessage.message?.stickerMessage) {
            const sticker = targetMessage.message.stickerMessage;
            const size = Math.round((sticker.fileLength || 0) / 1024);
            const isAnimated = sticker.isAnimated ? "Yes" : "No";

            return `<p><b>Sticker</b></p>
<p>From: ${esc(chatName)}</p>
<p>Size: ${size}KB</p>
<p>Animated: ${isAnimated}</p>
<p><b>Nokia Compatible:</b></p>
<p>
<a href="/wml/view-wbmp.wml?mid=${encodeURIComponent(
              messageId
            )}&amp;jid=${encodeURIComponent(jid)}">[WBMP View]</a>
<a href="/wml/media/${encodeURIComponent(messageId)}.jpg">[JPG]</a>
${sticker.isAnimated ? `<a href="/wml/media/${encodeURIComponent(messageId)}.gif">[GIF Animated]</a>` : ""}
</p>
<p><b>Other Formats:</b></p>
<p>
<a href="/wml/media/${encodeURIComponent(messageId)}.gif">[GIF]</a>
<a href="/wml/media/${encodeURIComponent(messageId)}.png">[PNG]</a>
</p>`;
          }

          return "<p><b>Unknown Media Type</b></p>";
        })()
      : `<p><b>Media Not Found</b></p>
<p>Message may have been deleted</p>
<p>Please try refreshing the chat</p>`;

    const body_full = `${body}
<p>
<a href="/wml/chat.wml?jid=${encodeURIComponent(
      jid
    )}" accesskey="0">[0] Back to Chat</a> 
<a href="/wml/chats.wml" accesskey="9">[9] All Chats</a>
</p>
<do type="accept" label="${t('common.back')}">
<go href="/wml/chat.wml?jid=${encodeURIComponent(jid)}"/>
</do>
<do type="options" label="${t('common.refresh')}">
<go href="/wml/media-info.wml?mid=${encodeURIComponent(
      messageId
    )}&amp;jid=${encodeURIComponent(jid)}"/>
</do>`;

    const wmlOutput = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
<head><meta http-equiv="Cache-Control" content="no-cache, no-store"/></head>
<card id="media" title="Media Info">
${body_full}
</card>
</wml>`;

    sendRawWmlAware(res, wmlOutput);
  } catch (error) {
    logger.error("Media info error:", error);
    res.status(500).send("Error loading media info");
  }
});

// ============ REALPLAYER STREAMING ENDPOINTS (.ram files) ============
// RAM files are playlist files that RealPlayer uses to stream media
// They contain URLs (HTTP or RTSP) that RealPlayer will open

// Serve .ram file for RealPlayer - Video with Audio
// Formats: 3gp (default, H.263+AMR), mp4 (H.264+AAC)
// Usage: /wml/stream/video/msgId.ram?format=3gp
app.get("/wml/stream/video/:messageId.ram", async (req, res) => {
  try {
    const { messageId } = req.params;
    // 3GP is best for Symbian RealPlayer (contains video + audio)
    const format = req.query.format || '3gp';
    const mode = req.query.mode || 'rtsp'; // rtsp (default) or http

    // Get server host without port for RTSP URL
    const hostHeader = req.headers.host || 'localhost:3000';
    const serverHost = hostHeader.split(':')[0];

    let videoUrl;
    if (mode === 'rtsp') {
      // RTSP URL for true streaming (RealPlayer native protocol)
      videoUrl = `rtsp://${serverHost}:${RTSP_PORT}/video/${encodeURIComponent(messageId)}.${format}`;
    } else {
      // HTTP fallback for progressive download
      const protocol = req.secure ? 'https' : 'http';
      videoUrl = `${protocol}://${hostHeader}/wml/media/${encodeURIComponent(messageId)}.${format}`;
    }

    console.log(`RealPlayer video RAM: ${messageId} -> ${videoUrl} (format: ${format}, mode: ${mode})`);

    // RAM file is plain text with URL(s), one per line
    res.setHeader("Content-Type", "audio/x-pn-realaudio");
    res.setHeader("Content-Disposition", `attachment; filename="video.ram"`);
    res.send(videoUrl + "\r\n");
  } catch (error) {
    console.error("RAM video error:", error);
    res.status(500).send("Error");
  }
});

// Serve .ram file for RealPlayer - Audio only
// Formats: amr (default, best for Symbian), mp3, wav, 3gp (audio track only)
// Usage: /wml/stream/audio/msgId.ram?format=amr
app.get("/wml/stream/audio/:messageId.ram", async (req, res) => {
  try {
    const { messageId } = req.params;
    // AMR is native Symbian format, best compatibility
    const format = req.query.format || 'amr';
    const mode = req.query.mode || 'rtsp'; // rtsp (default) or http

    // Get server host without port for RTSP URL
    const hostHeader = req.headers.host || 'localhost:3000';
    const serverHost = hostHeader.split(':')[0];

    let audioUrl;
    if (mode === 'rtsp') {
      // RTSP URL for true streaming (RealPlayer native protocol)
      audioUrl = `rtsp://${serverHost}:${RTSP_PORT}/audio/${encodeURIComponent(messageId)}.${format}`;
    } else {
      // HTTP fallback for progressive download
      const protocol = req.secure ? 'https' : 'http';
      audioUrl = `${protocol}://${hostHeader}/wml/media/${encodeURIComponent(messageId)}.${format}`;
    }

    console.log(`RealPlayer audio RAM: ${messageId} -> ${audioUrl} (format: ${format}, mode: ${mode})`);

    res.setHeader("Content-Type", "audio/x-pn-realaudio");
    res.setHeader("Content-Disposition", `attachment; filename="audio.ram"`);
    res.send(audioUrl + "\r\n");
  } catch (error) {
    console.error("RAM audio error:", error);
    res.status(500).send("Error");
  }
});

// Universal RAM endpoint - works for both video and audio
// Usage: /wml/stream/msgId.ram?type=video&format=3gp
//        /wml/stream/msgId.ram?type=audio&format=amr
app.get("/wml/stream/:messageId.ram", async (req, res) => {
  try {
    const { messageId } = req.params;
    const type = req.query.type || 'video';
    // Default format based on type
    const format = req.query.format || (type === 'video' ? '3gp' : 'amr');
    const mode = req.query.mode || 'rtsp'; // rtsp (default) or http

    // Get server host without port for RTSP URL
    const hostHeader = req.headers.host || 'localhost:3000';
    const serverHost = hostHeader.split(':')[0];

    let mediaUrl;
    if (mode === 'rtsp') {
      // RTSP URL for true streaming (RealPlayer native protocol)
      mediaUrl = `rtsp://${serverHost}:${RTSP_PORT}/${type}/${encodeURIComponent(messageId)}.${format}`;
    } else {
      // HTTP fallback for progressive download
      const protocol = req.secure ? 'https' : 'http';
      mediaUrl = `${protocol}://${hostHeader}/wml/media/${encodeURIComponent(messageId)}.${format}`;
    }

    console.log(`RealPlayer RAM (${type}): ${messageId} -> ${mediaUrl} (mode: ${mode})`);

    res.setHeader("Content-Type", "audio/x-pn-realaudio");
    res.setHeader("Content-Disposition", `attachment; filename="${type}.ram"`);
    res.send(mediaUrl + "\r\n");
  } catch (error) {
    console.error("RAM stream error:", error);
    res.status(500).send("Error");
  }
});

// Direct 3GP download (for RealPlayer direct link)
app.get("/wml/play/:messageId.3gp", async (req, res) => {
  authRedirect(res, `/wml/media/${req.params.messageId}.3gp`);
});

// Direct MP3 download (for RealPlayer direct link)
app.get("/wml/play/:messageId.mp3", async (req, res) => {
  authRedirect(res, `/wml/media/${req.params.messageId}.mp3`);
});

// Direct AMR download (for RealPlayer/Symbian direct link)
app.get("/wml/play/:messageId.amr", async (req, res) => {
  authRedirect(res, `/wml/media/${req.params.messageId}.amr`);
});

// Direct MP4 download (for RealPlayer direct link)
app.get("/wml/play/:messageId.mp4", async (req, res) => {
  authRedirect(res, `/wml/media/${req.params.messageId}.mp4`);
});

// Direct WAV download
app.get("/wml/play/:messageId.wav", async (req, res) => {
  authRedirect(res, `/wml/media/${req.params.messageId}.wav`);
});

// Alternative: RTSP-style redirect for RealPlayer (opens media directly)
app.get("/wml/rtsp/:messageId", async (req, res) => {
  try {
    const { messageId } = req.params;
    const type = req.query.type || 'video'; // video or audio
    // Default to AMR for audio (better Symbian compatibility)
    const format = req.query.format || (type === 'video' ? '3gp' : 'amr');

    const host = req.headers.host || 'localhost:3000';
    const protocol = req.secure ? 'https' : 'http';

    const mediaUrl = `${protocol}://${host}/wml/media/${encodeURIComponent(messageId)}.${format}`;

    console.log(`RTSP redirect for ${type}: ${messageId} -> ${mediaUrl}`);

    // Redirect to the actual media file
    res.redirect(302, mediaUrl);
  } catch (error) {
    console.error("RTSP redirect error:", error);
    res.status(500).send("Redirect error");
  }
});

// ============ OPERA MINI / NOKIA SYMBIAN - MEDIA UPLOAD (SSR-ONLY) ============
// Pure server-side rendering — Opera Mini has JS but runs it on proxy.
// All processing happens server-side: Busboy parses multipart stream, server sends to WhatsApp.
// Busboy responds with 303 redirect as soon as fields are parsed (before file upload completes),
// so Opera Mini sees the status page almost immediately after pressing submit.

// Opera Mini - Send media form (solo upload, niente ricerca)
app.get("/opera/send", async (req, res) => {
  const jid = req.query.jid || '';

  // O(1) — early-exit guards before any computation
  if (!sock) {
    return res.send(operaResultPage(t('opera.disconnected'), t('opera.not_connected'), null));
  }

  if (!jid) {
    return res.send(operaResultPage(t('common.error'), t('opera.no_recipient'), null));
  }

  // O(1) — Map lookup for contact name
  const contact = contactStore.get(jid);
  const name = contact?.name || contact?.notify || jid.split('@')[0];
  const escapedName = name.replace(/</g, '&lt;').replace(/>/g, '&gt;');

  // Check if there's a cached file for this jid
  const cached = uploadFileCache.get(jid);
  const cachedHtml = cached && fs.existsSync(cached.path) ? (() => {
    const escapedFilename = cached.originalname.replace(/</g, '&lt;').replace(/>/g, '&gt;');
    const sizeKB = (cached.size / 1024).toFixed(1);
    return `
  <div class="s" style="background:#e8f5e9;border-color:#25d366">
    <h2>${t('opera.cached_file')}</h2>
    <p class="note"><b>${escapedFilename}</b> (${sizeKB} KB)</p>
    <p class="note">${t('opera.cached_resend_note')}</p>
    <form method="post" action="/opera/upload" enctype="multipart/form-data">
      <input type="hidden" name="jid" value="${jid}">
      <input type="hidden" name="useCached" value="1">
      <label>${t('opera.type_label')}</label>
      <select name="type" style="width:100%;padding:5px;margin-bottom:10px">
        <option value="image">${t('opera.type_image')}</option>
        <option value="audio">${t('opera.type_audio')}</option>
        <option value="video">${t('opera.type_video')}</option>
        <option value="document">${t('opera.type_document')}</option>
        <option value="file">${t('opera.type_file')}</option>
      </select>
      <label>${t('opera.caption_optional')}</label>
      <input type="text" name="caption" placeholder="${t('opera.caption_optional_placeholder')}">
      <input type="submit" value="${t('opera.resend_cached')}">
    </form>
  </div>`;
  })() : '';

  // XHTML mode: simple form without JS/CSS/SVG
  if (UPLOAD_MARKUP_MODE === 'xhtml') {
    const cachedXhtml = cached && fs.existsSync(cached.path) ? (() => {
      const escapedFilename = cached.originalname.replace(/</g, '&lt;').replace(/>/g, '&gt;');
      const sizeKB = (cached.size / 1024).toFixed(1);
      return `
<div class="cached-section">
  <h2>${t('opera.cached_file')}</h2>
  <p><b>${escapedFilename}</b> (${sizeKB} KB)</p>
  <p>${t('opera.cached_resend_note')}</p>
  <form method="post" action="/opera/upload" enctype="multipart/form-data">
    <input type="hidden" name="jid" value="${jid}"/>
    <input type="hidden" name="useCached" value="1"/>
    <input type="hidden" name="xhtml" value="1"/>
    <label>${t('opera.type_label')}</label>
    <select name="type">
      <option value="image">${t('opera.type_image')}</option>
      <option value="audio">${t('opera.type_audio')}</option>
      <option value="video">${t('opera.type_video')}</option>
      <option value="document">${t('opera.type_document')}</option>
      <option value="file">${t('opera.type_file')}</option>
    </select>
    <label>${t('opera.caption_optional')}</label>
    <input type="text" name="caption"/>
    <input type="submit" class="btn-send" value="${t('opera.resend_cached')}"/>
  </form>
</div>`;
    })() : '';

    // Upload page: no XML prolog, served as text/html for multipart form compatibility.
    // Uses XHTML-MP DOCTYPE but with text/html Content-Type to avoid form upload issues
    // on Nokia WAP 2.0 browser and Opera Mini.
    const xhtml = `<!DOCTYPE html PUBLIC "-//WAPFORUM//DTD XHTML Mobile 1.0//EN" "http://www.wapforum.org/DTD/xhtml-mobile10.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
  <meta http-equiv="Content-Type" content="text/html; charset=utf-8"/>
  <title>${t('opera.page_title')} ${t('opera.to')} ${escapedName}</title>
  <style type="text/css">${XHTML_CSS}</style>
</head>
<body>
<div class="wa-bar">${t('opera.page_title')} <small>${t('opera.to')} ${escapedName}</small></div>

${cachedXhtml}

<form method="post" action="/opera/upload" enctype="multipart/form-data" onsubmit="try{document.getElementById('xhtml-upload-wait').style.display='block';document.getElementById('xhtml-upload-form-section').style.display='none';}catch(e){}">
  <div id="xhtml-upload-form-section">
  <p>
    <input type="hidden" name="jid" value="${jid}"/>
    <input type="hidden" name="xhtml" value="1"/>
    ${t('opera.type_label')}<br/>
    <select name="type">
      <option value="image">${t('opera.type_image')}</option>
      <option value="audio">${t('opera.type_audio')}</option>
      <option value="video">${t('opera.type_video')}</option>
      <option value="document">${t('opera.type_document')}</option>
      <option value="file">${t('opera.type_file')}</option>
    </select><br/>
    ${t('opera.caption_optional')}<br/>
    <input type="text" name="caption"/><br/>
    <input name="media" type="file"/><br/>
  </p>
  <p>
    <input type="submit" value="${t('opera.send_normal')}"/>
  </p>
  </div>
</form>

<div id="xhtml-upload-wait" style="display:none">
  <p><b>${t('opera.upload_wait_msg')}</b></p>
  <p>[####################] ...</p>
  <p><small>${t('opera.phase_receiving')}</small></p>
</div>

<a class="back-link" href="/wml/chat.wml?jid=${encodeURIComponent(jid)}">${t('common.back')}</a>
</body>
</html>`;

    // Serve as text/html for maximum browser compatibility with multipart form uploads.
    // application/xhtml+xml causes some browsers to mishandle multipart/form-data submissions.
    res.setHeader("Content-Type", "text/html; charset=utf-8");
    return res.send(xhtml);
  }

  const html = `<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width,initial-scale=1">
  <title>${t('opera.page_title')} ${t('opera.to')} ${escapedName}</title>
  ${WAP_FAVICON_LINK}
  <style>
    *{box-sizing:border-box}
    body{font-family:Arial,sans-serif;margin:0;font-size:14px;background:#e5ddd5}
    .hdr{background:#075e54;color:#fff;padding:12px 16px;font-size:16px;font-weight:700}
    .hdr small{font-size:12px;opacity:.8;display:block;margin-top:2px}
    .wrap{padding:10px;max-width:480px;margin:0 auto}
    .s{background:#fff;border-radius:10px;padding:14px;margin-bottom:10px;border:1px solid #e0e0e0;box-shadow:0 1px 3px rgba(0,0,0,.07)}
    .s-hdr{display:flex;align-items:center;gap:8px;margin-bottom:12px;padding-bottom:10px;border-bottom:1px solid #f0f0f0}
    .s-hdr h2{font-size:15px;font-weight:700;margin:0;color:#075e54}
    label{display:block;margin:8px 0 3px;font-weight:700;font-size:12px;color:#555;text-transform:uppercase;letter-spacing:.4px}
    input[type=file]{width:100%;margin-bottom:6px;font-size:13px}
    input[type=text]{width:100%;padding:8px 10px;margin-bottom:6px;border:1px solid #ccc;border-radius:6px;font-size:13px}
    select{width:100%;padding:8px 10px;margin-bottom:6px;border:1px solid #ccc;border-radius:6px;font-size:13px}
    .btn-row{display:flex;flex-direction:column;gap:7px;margin-top:10px}
    .btn-n,.btn-s,.btn-p{display:flex;align-items:center;gap:10px;border:0;padding:12px 16px;font-size:14px;font-weight:700;width:100%;border-radius:8px;cursor:pointer;color:#fff;text-align:left;line-height:1.2}
    .btn-n{background:#25d366}
    .btn-p{background:#2980b9}
    .btn-s{background:#8e44ad}
    .btn-n:hover{background:#1ebe5b}
    .btn-p:hover{background:#2471a3}
    .btn-s:hover{background:#7d3c98}
    .btn-n:disabled,.btn-p:disabled,.btn-s:disabled{opacity:.45;cursor:default}
    .btn-lbl{flex:1}
    .btn-sub{display:block;font-size:11px;font-weight:400;opacity:.8;margin-top:1px}
    .prog{margin:10px 0;display:none}
    .prog-bar{background:#e0e0e0;border-radius:6px;height:22px;overflow:hidden;position:relative}
    .prog-fill{background:#2980b9;height:100%;width:0%;border-radius:6px}
    .prog-lbl{position:absolute;top:0;left:0;right:0;text-align:center;line-height:22px;font-size:11px;color:#fff;font-weight:700}
    .prog-msg{font-size:11px;color:#666;margin-top:4px;text-align:center}
    .note{color:#888;font-size:11px;margin:4px 0}
  </style>
</head>
<body>
  <div class="hdr">
    <svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" style="vertical-align:-3px;margin-right:6px"><line x1="22" y1="2" x2="11" y2="13"/><polygon points="22 2 15 22 11 13 2 9 22 2"/></svg>${t('opera.page_title')}
    <small>${t('opera.to')} ${escapedName}</small>
  </div>
  <div class="wrap">
  ${cachedHtml}

  <div class="s">
    <div class="s-hdr">
      <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="#075e54" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M23 19a2 2 0 0 1-2 2H3a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h4l2-3h6l2 3h4a2 2 0 0 1 2 2z"/><circle cx="12" cy="13" r="4"/></svg>
      <h2>${t('opera.image')}</h2>
    </div>
    <form method="post" action="/opera/upload" enctype="multipart/form-data">
      <input type="hidden" name="jid" value="${jid}">
      <input type="hidden" name="type" value="image">
      <input type="file" name="media" accept="image/*">
      <label>${t('opera.caption')}</label>
      <input type="text" name="caption" placeholder="${t('opera.caption_placeholder')}">
      <div class="btn-row">
        <button type="submit" class="btn-n">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><line x1="22" y1="2" x2="11" y2="13"/><polygon points="22 2 15 22 11 13 2 9 22 2"/></svg>
          <span class="btn-lbl">${t('opera.send_normal')}<span class="btn-sub">${t('opera.send_normal_sub')}</span></span>
        </button>
        <button type="button" class="btn-s" onclick="uploadChunked(this,1,16384)">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="16 16 12 12 8 16"/><line x1="12" y1="12" x2="12" y2="21"/><path d="M20.39 18.39A5 5 0 0 0 18 9h-1.26A8 8 0 1 0 3 16.3"/></svg>
          <span class="btn-lbl">${t('opera.send_sequential')}<span class="btn-sub">${t('opera.send_sequential_sub')}</span></span>
        </button>
        <button type="button" class="btn-p" onclick="uploadChunked(this,3,16384)">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polygon points="13 2 3 14 12 14 11 22 21 10 12 10 13 2"/></svg>
          <span class="btn-lbl">${t('opera.send_parallel')}<span class="btn-sub">${t('opera.send_parallel_sub')}</span></span>
        </button>
      </div>
      <div class="prog"><div class="prog-bar"><div class="prog-fill"></div><div class="prog-lbl">0%</div></div><div class="prog-msg">${t('opera.progress_starting')}</div></div>
    </form>
  </div>

  <div class="s">
    <div class="s-hdr">
      <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="#075e54" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M9 18V5l12-2v13"/><circle cx="6" cy="18" r="3"/><circle cx="18" cy="16" r="3"/></svg>
      <h2>${t('opera.audio')}</h2>
    </div>
    <form method="post" action="/opera/upload" enctype="multipart/form-data">
      <input type="hidden" name="jid" value="${jid}">
      <input type="hidden" name="type" value="audio">
      <input type="file" name="media" accept="audio/*">
      <div class="btn-row">
        <button type="submit" class="btn-n">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><line x1="22" y1="2" x2="11" y2="13"/><polygon points="22 2 15 22 11 13 2 9 22 2"/></svg>
          <span class="btn-lbl">${t('opera.send_normal')}<span class="btn-sub">${t('opera.send_normal_sub')}</span></span>
        </button>
        <button type="button" class="btn-s" onclick="uploadChunked(this,1,16384)">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="16 16 12 12 8 16"/><line x1="12" y1="12" x2="12" y2="21"/><path d="M20.39 18.39A5 5 0 0 0 18 9h-1.26A8 8 0 1 0 3 16.3"/></svg>
          <span class="btn-lbl">${t('opera.send_sequential')}<span class="btn-sub">${t('opera.send_sequential_sub')}</span></span>
        </button>
        <button type="button" class="btn-p" onclick="uploadChunked(this,3,16384)">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polygon points="13 2 3 14 12 14 11 22 21 10 12 10 13 2"/></svg>
          <span class="btn-lbl">${t('opera.send_parallel')}<span class="btn-sub">${t('opera.send_parallel_sub')}</span></span>
        </button>
      </div>
      <div class="prog"><div class="prog-bar"><div class="prog-fill"></div><div class="prog-lbl">0%</div></div><div class="prog-msg">${t('opera.progress_starting')}</div></div>
    </form>
  </div>

  <div class="s">
    <div class="s-hdr">
      <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="#075e54" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polygon points="23 7 16 12 23 17 23 7"/><rect x="1" y="5" width="15" height="14" rx="2" ry="2"/></svg>
      <h2>${t('opera.video')}</h2>
    </div>
    <form method="post" action="/opera/upload" enctype="multipart/form-data">
      <input type="hidden" name="jid" value="${jid}">
      <input type="hidden" name="type" value="video">
      <input type="file" name="media" accept="video/*">
      <label>${t('opera.caption')}</label>
      <input type="text" name="caption" placeholder="${t('opera.caption_placeholder')}">
      <div class="btn-row">
        <button type="submit" class="btn-n">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><line x1="22" y1="2" x2="11" y2="13"/><polygon points="22 2 15 22 11 13 2 9 22 2"/></svg>
          <span class="btn-lbl">${t('opera.send_normal')}<span class="btn-sub">${t('opera.send_normal_sub')}</span></span>
        </button>
        <button type="button" class="btn-s" onclick="uploadChunked(this,1,16384)">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="16 16 12 12 8 16"/><line x1="12" y1="12" x2="12" y2="21"/><path d="M20.39 18.39A5 5 0 0 0 18 9h-1.26A8 8 0 1 0 3 16.3"/></svg>
          <span class="btn-lbl">${t('opera.send_sequential')}<span class="btn-sub">${t('opera.send_sequential_sub')}</span></span>
        </button>
        <button type="button" class="btn-p" onclick="uploadChunked(this,3,16384)">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polygon points="13 2 3 14 12 14 11 22 21 10 12 10 13 2"/></svg>
          <span class="btn-lbl">${t('opera.send_parallel')}<span class="btn-sub">${t('opera.send_parallel_sub')}</span></span>
        </button>
      </div>
      <div class="prog"><div class="prog-bar"><div class="prog-fill"></div><div class="prog-lbl">0%</div></div><div class="prog-msg">${t('opera.progress_starting')}</div></div>
    </form>
  </div>

  <div class="s">
    <div class="s-hdr">
      <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="#075e54" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"/><polyline points="14 2 14 8 20 8"/><line x1="16" y1="13" x2="8" y2="13"/><line x1="16" y1="17" x2="8" y2="17"/></svg>
      <h2>${t('opera.document')}</h2>
    </div>
    <form method="post" action="/opera/upload" enctype="multipart/form-data">
      <input type="hidden" name="jid" value="${jid}">
      <input type="hidden" name="type" value="document">
      <input type="file" name="media">
      <div class="btn-row">
        <button type="submit" class="btn-n">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><line x1="22" y1="2" x2="11" y2="13"/><polygon points="22 2 15 22 11 13 2 9 22 2"/></svg>
          <span class="btn-lbl">${t('opera.send_normal')}<span class="btn-sub">${t('opera.send_normal_sub')}</span></span>
        </button>
        <button type="button" class="btn-s" onclick="uploadChunked(this,1,16384)">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="16 16 12 12 8 16"/><line x1="12" y1="12" x2="12" y2="21"/><path d="M20.39 18.39A5 5 0 0 0 18 9h-1.26A8 8 0 1 0 3 16.3"/></svg>
          <span class="btn-lbl">${t('opera.send_sequential')}<span class="btn-sub">${t('opera.send_sequential_sub')}</span></span>
        </button>
        <button type="button" class="btn-p" onclick="uploadChunked(this,3,16384)">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polygon points="13 2 3 14 12 14 11 22 21 10 12 10 13 2"/></svg>
          <span class="btn-lbl">${t('opera.send_parallel')}<span class="btn-sub">${t('opera.send_parallel_sub')}</span></span>
        </button>
      </div>
      <div class="prog"><div class="prog-bar"><div class="prog-fill"></div><div class="prog-lbl">0%</div></div><div class="prog-msg">${t('opera.progress_starting')}</div></div>
    </form>
  </div>

  <div class="s">
    <div class="s-hdr">
      <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="#075e54" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="21 8 21 21 3 21 3 8"/><rect x="1" y="3" width="22" height="5"/><line x1="10" y1="12" x2="14" y2="12"/></svg>
      <h2>${t('opera.generic_file')}</h2>
    </div>
    <p class="note">${t('opera.generic_file_note')}</p>
    <form method="post" action="/opera/upload" enctype="multipart/form-data">
      <input type="hidden" name="jid" value="${jid}">
      <input type="hidden" name="type" value="file">
      <input type="file" name="media">
      <div class="btn-row">
        <button type="submit" class="btn-n">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><line x1="22" y1="2" x2="11" y2="13"/><polygon points="22 2 15 22 11 13 2 9 22 2"/></svg>
          <span class="btn-lbl">${t('opera.send_normal')}<span class="btn-sub">${t('opera.send_normal_sub')}</span></span>
        </button>
        <button type="button" class="btn-s" onclick="uploadChunked(this,1,16384)">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="16 16 12 12 8 16"/><line x1="12" y1="12" x2="12" y2="21"/><path d="M20.39 18.39A5 5 0 0 0 18 9h-1.26A8 8 0 1 0 3 16.3"/></svg>
          <span class="btn-lbl">${t('opera.send_sequential')}<span class="btn-sub">${t('opera.send_sequential_sub')}</span></span>
        </button>
        <button type="button" class="btn-p" onclick="uploadChunked(this,3,16384)">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polygon points="13 2 3 14 12 14 11 22 21 10 12 10 13 2"/></svg>
          <span class="btn-lbl">${t('opera.send_parallel')}<span class="btn-sub">${t('opera.send_parallel_sub')}</span></span>
        </button>
      </div>
      <div class="prog"><div class="prog-bar"><div class="prog-fill"></div><div class="prog-lbl">0%</div></div><div class="prog-msg">${t('opera.progress_starting')}</div></div>
    </form>
  </div>
  </div>

<script type="text/javascript">
(function() {
  var CHUNK     = 16384;  // 32 KB per chunk
  var PAR       = 3;      // chunk paralleli simultanei
  var MAX_RETRY = 3;      // tentativi per chunk prima di abbandonare

  function genId() {
    return Date.now().toString(36) + Math.random().toString(36).substr(2, 9);
  }

  function getForm(el) {
    while (el && el.tagName !== 'FORM') el = el.parentNode;
    return el;
  }

  function getField(form, name) {
    var els = form.elements;
    for (var i = 0; i < els.length; i++) if (els[i].name === name) return els[i];
    return null;
  }

  function setProg(form, msg, pct) {
    var d = form.querySelector('.prog');
    if (!d) return;
    d.style.display = 'block';
    var fill  = d.querySelector('.prog-fill');
    var lbl   = d.querySelector('.prog-lbl');
    var msgEl = d.querySelector('.prog-msg');
    if (fill)  fill.style.width   = pct + '%';
    if (lbl)   lbl.textContent    = Math.round(pct) + '%';
    if (msgEl) msgEl.textContent  = msg;
  }

  function setBtns(form, disabled) {
    var bs = form.querySelectorAll('input[type=submit], button');
    for (var i = 0; i < bs.length; i++) bs[i].disabled = disabled;
  }

  window.uploadChunked = function(btn, par, chunkSize) {
    var parallelism = (par && par > 0) ? par : 3;
    var chunkBytes_sz = (chunkSize && chunkSize > 0) ? chunkSize : CHUNK;
    var form = getForm(btn);
    if (!form) return;

    var fi = getField(form, 'media');
    if (!fi || !fi.files || !fi.files[0]) { alert('Seleziona prima un file.'); return; }

    var file    = fi.files[0];
    var to      = (getField(form, 'jid') || getField(form, 'to') || {value:''}).value;
    var type    = (getField(form, 'type') || {value:'document'}).value;
    var capEl   = getField(form, 'caption');
    var caption = capEl ? capEl.value : '';

    var uploadId    = genId();
    var totalChunks = Math.max(1, Math.ceil(file.size / chunkBytes_sz));
    var completed   = 0;   // chunk completati con successo
    var failed      = false;
    var qIdx        = 0;
    var active      = 0;

    // Traccia i byte caricati per ciascun chunk attivo (per barra smooth)
    var chunkBytes = {}; // chunkIndex -> bytes caricati finora

    setBtns(form, true);
    setProg(form, '${t('opera.progress_starting')}', 0);

    // Aggiorna la barra sommando i byte di tutti i chunk attivi + quelli completati
    function refreshBar() {
      var loaded = completed * chunkBytes_sz; // byte dei chunk gia completati (approssimato)
      for (var k in chunkBytes) loaded += chunkBytes[k];
      var pct = Math.min(100, (loaded / file.size) * 100);
      setProg(form, 'Chunk ' + completed + '/' + totalChunks + ' (' + Math.round(pct) + '%)', pct);
    }

    // Invia un singolo chunk, con retry automatico fino a MAX_RETRY volte
    function sendChunk(idx, attempt, cb) {
      var start    = idx * chunkBytes_sz;
      var end      = Math.min(start + chunkBytes_sz, file.size);
      var sliceFn  = file.slice || file.webkitSlice || file.mozSlice;
      var blob     = sliceFn.call(file, start, end);

      var fd = new FormData();
      fd.append('uploadId',    uploadId);
      fd.append('chunkIndex',  idx);
      fd.append('totalChunks', totalChunks);
      fd.append('to',          to);
      fd.append('type',        type);
      fd.append('caption',     caption);
      fd.append('filename',    file.name);
      fd.append('mimetype',    file.type || 'application/octet-stream');
      fd.append('filesize',    file.size);
      fd.append('chunk',       blob);

      chunkBytes[idx] = 0;

      // Guard: onerror + onreadystatechange both fire on network errors.
      // settled prevents double-call of onFail/success which would corrupt
      // active/completed counters (critical in serial mode where PAR=1).
      var settled = false;

      var xhr = new XMLHttpRequest();
      xhr.open('POST', '/opera/upload-chunk', true);
      xhr.timeout = 120000; // 120s per chunk (margine per 2G/GPRS)

      // Progresso byte-level per questo chunk (smooth bar)
      // xhr.upload may be undefined in Opera Mini / older browsers — guard required
      if (xhr.upload) {
        xhr.upload.onprogress = function(e) {
          if (e.lengthComputable) {
            chunkBytes[idx] = e.loaded;
            refreshBar();
          }
        };
      }

      function onFail() {
        if (settled) return;
        settled = true;
        delete chunkBytes[idx];
        if (attempt < MAX_RETRY) {
          setProg(form, 'Retry chunk ' + idx + ' (tentativo ' + (attempt + 1) + ')...', 0);
          setTimeout(function() { sendChunk(idx, attempt + 1, cb); }, 1000 * Math.pow(2, attempt));
        } else {
          cb(new Error('Chunk ' + idx + ' fallito dopo ' + MAX_RETRY + ' tentativi'));
        }
      }

      xhr.onreadystatechange = function() {
        if (xhr.readyState !== 4) return;
        if (settled) return;
        settled = true;
        delete chunkBytes[idx];
        if (xhr.status === 200) {
          cb(null);
        } else {
          onFail();
        }
      };

      xhr.onerror   = onFail;
      xhr.ontimeout = onFail;

      xhr.send(fd);
    }

    function dispatch() {
      if (failed) return;
      while (active < parallelism && qIdx < totalChunks) {
        (function(i) {
          active++;
          sendChunk(i, 1, function(err) {
            active--;
            if (failed) return;
            if (err) {
              failed = true;
              setProg(form, '${t('opera.error_prefix')}' + err.message + '${t('opera.error_suffix')}', 0);
              setBtns(form, false);
              return;
            }
            completed++;
            refreshBar();
            if (completed >= totalChunks) {
              setProg(form, 'Upload completato! Apertura stato...', 100);
              setTimeout(function() {
                window.location.href = '/opera/upload-status?id=' + uploadId;
              }, 300);
              return;
            }
            dispatch();
          });
        })(qIdx++);
      }
    }

    try {
      dispatch();
    } catch (e) {
      setProg(form, '${t('opera.error_prefix')}' + (e.message || e), 0);
      setBtns(form, false);
    }
  };
})();
</script>
</body>
</html>`;

  res.setHeader("Content-Type", "text/html; charset=utf-8");
  res.send(html);
});

// SSR upload handler — server does all processing, returns plain HTML result page.
// No client-side JS needed. Nokia/Symbian native form POST -> multer parses -> server sends to WhatsApp -> HTML response.
//
// TIME COMPLEXITY:
//   Validation: O(1) — constant-time guards, Set lookup, string prefix check
//   File read:  O(N) where N = file size in bytes — single sequential read, unavoidable
//   Audio conversion: O(N) — FFmpeg single-pass transcode, linear in input size
//   Image/Video/Doc: O(1) — no conversion, direct buffer pass-through
//   Cleanup: O(1) — single unlink call
//   Total: O(N) dominated by file I/O
//
// SPACE COMPLEXITY:
//   O(N) where N = file size — one buffer in memory at a time
//   Audio conversion: O(N) peak — input buffer freed before reading output buffer
//   No redundant copies: multer writes to disk, we read once, send, then delete

// O(1) Set for native audio format detection — avoids O(K) repeated .includes() per mime string
const NATIVE_AUDIO_FORMATS = new Set(['ogg', 'amr', '3gpp', 'opus']);

// O(1) Map for type labels — avoids chained ternaries at O(K) string comparisons
const TYPE_LABEL_KEYS = new Map([['image', 'opera.type_image'], ['audio', 'opera.type_audio'], ['video', 'opera.type_video'], ['document', 'opera.type_document'], ['file', 'opera.type_file']]);

// ============ CUSTOM WAP FAVICON & THUMBNAIL ============
// WhatsApp-style green phone icon as inline SVG → data URI (no external files needed)
// Compatible with all browsers including Opera Mini, Nokia, Symbian
const WAP_FAVICON_SVG = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 64 64"><rect width="64" height="64" rx="14" fill="#25d366"/><path d="M32 12C21 12 12 20.7 12 31.4c0 3.6 1 7 2.8 10L12 52l11-2.8c3 1.6 6.3 2.4 9.8 2.4C43.5 51.6 52 42.9 52 31.4S43.5 12 32 12zm0 35.6c-3 0-5.8-.8-8.2-2.2l-.6-.3-6.2 1.6 1.7-6-.4-.6c-1.6-2.5-2.5-5.5-2.5-8.7 0-8.8 7.2-16 16.2-16s16.2 7.2 16.2 16-7.4 16.2-16.2 16.2zm8.8-12c-.5-.2-2.8-1.4-3.3-1.5-.4-.2-.8-.2-1.1.2-.3.5-1.2 1.5-1.5 1.8-.3.3-.5.4-1 .1-.5-.2-2-.7-3.8-2.3-1.4-1.2-2.3-2.8-2.6-3.3-.3-.5 0-.7.2-1 .2-.2.5-.5.7-.8.2-.3.3-.5.4-.8.2-.3 0-.6 0-.8-.1-.3-1.1-2.7-1.5-3.7-.4-1-.8-1-1.1-1h-1c-.3 0-.8.1-1.2.6s-1.6 1.5-1.6 3.8c0 2.2 1.6 4.4 1.8 4.7.3.3 3.2 4.8 7.7 6.7 1.1.5 1.9.7 2.6.9 1.1.3 2 .3 2.8.2.8-.1 2.8-1.1 3.2-2.2.4-1.1.4-2 .3-2.2-.2-.2-.5-.3-1-.5z" fill="#fff"/></svg>`;
// Favicon HTML link tag — inject into <head> of all HTML pages
const WAP_FAVICON_LINK = `<link rel="icon" type="image/svg+xml" href="/favicon.svg"><link rel="shortcut icon" href="/favicon.svg"><link rel="apple-touch-icon" href="/favicon.svg">`;

// Serve favicon as SVG for all browsers
let _faviconBuffer = null;

// SSR upload progress tracking — Map<jobId, {status, percent, message, jid, type, done, error}>
// O(1) per get/set/delete. Space: O(J) where J = active jobs. Auto-expire prevents unbounded growth.
const uploadJobs = new Map();

// SSR upload file cache — Map<jid, {path, originalname, mimetype, size, timestamp}>
// Caches the last uploaded file per jid so user doesn't need to reselect after an error.
// O(1) per get/set/delete. Auto-expires after 30 min.
const uploadFileCache = new Map();

// WhatsApp per-type size limits (bytes)
const WA_UPLOAD_SIZE_LIMITS = { image: 16 * 1024 * 1024, video: 64 * 1024 * 1024, audio: 16 * 1024 * 1024, document: 64 * 1024 * 1024 };

// Chunk upload sessions — Map<uploadId, { received: Set<number>, total, to, type, caption, filename, mimetype, filesize, processed }>
const chunkSessions = new Map();

// ---- Shared processing function — called by both single-request and chunked upload ----
// meta: { path, originalname, mimetype, size, _fromCache? }
async function processUploadJob(jobId, meta, to, type, caption) {
  const job = uploadJobs.get(jobId);
  if (!job) return;

  console.log(`[Upload] Job ${jobId}: ${meta.originalname}, type=${type}, mime=${meta.mimetype}, size=${meta.size}, to=${to}`);

  try {
    job.percent = 45; job.status = t('opera.status_reading');
    let mediaBuffer = await fs.promises.readFile(meta.path);
    const formattedJid = formatJid(to);

    if (type === 'image') {
      if (!SUPPORTED_IMAGE_TYPES.has(meta.mimetype)) {
        throw new Error(`${t('opera.unsupported_image')} ${meta.mimetype}. ${t('opera.use_formats')}`);
      }
      job.percent = 65; job.status = t('opera.status_sending_image');
      await sock.sendMessage(formattedJid, { image: mediaBuffer, caption: caption || undefined, mimetype: meta.mimetype });
    }
    else if (type === 'audio') {
      const mimeSubtype = meta.mimetype.split('/')[1] || '';
      const isNative = NATIVE_AUDIO_FORMATS.has(mimeSubtype) || NATIVE_AUDIO_FORMATS.has(mimeSubtype.split(';')[0]);
      if (isNative) {
        job.percent = 65; job.status = t('opera.status_sending_audio');
        await sock.sendMessage(formattedJid, { audio: mediaBuffer, ptt: true, mimetype: 'audio/ogg; codecs=opus' });
      } else {
        job.percent = 50; job.status = t('opera.status_converting_audio');
        const ts = Date.now();
        const tempIn  = safeTempPath(`audio_${ts}.${mimeSubtype || 'bin'}`);
        const tempOut = safeTempPath(`audio_${ts}.ogg`);
        try {
          await fs.promises.writeFile(tempIn, mediaBuffer); mediaBuffer = null;
          await new Promise((resolve, reject) => {
            const proc = spawn(ffmpeg, ['-y', '-i', tempIn, '-c:a', 'libopus', '-b:a', '128k', '-ar', '48000', '-ac', '1', '-vbr', 'on', '-compression_level', '3', '-application', 'audio', tempOut]);
            let stderr = '';
            proc.stderr.on('data', (d) => { stderr += d.toString(); });
            proc.on('close', (code) => code === 0 ? resolve() : reject(new Error(`FFmpeg audio: ${stderr.slice(-200)}`)));
            proc.on('error', reject);
          });
          job.percent = 75; job.status = t('opera.status_sending_audio');
          const oggBuffer = await fs.promises.readFile(tempOut);
          console.log(`[Upload] Job ${jobId}: audio converted ${oggBuffer.length} bytes`);
          await sock.sendMessage(formattedJid, { audio: oggBuffer, mimetype: 'audio/ogg; codecs=opus', ptt: true });
        } catch (convErr) {
          console.error(`[Upload] Job ${jobId}: audio conv failed:`, convErr);
          job.percent = 75; job.status = t('opera.status_conv_failed');
          const fallback = mediaBuffer || await fs.promises.readFile(meta.path);
          await sock.sendMessage(formattedJid, { document: fallback, mimetype: meta.mimetype, fileName: meta.originalname });
        } finally {
          fs.promises.unlink(tempIn).catch(() => {});
          fs.promises.unlink(tempOut).catch(() => {});
        }
      }
    }
    else if (type === 'video') {
      job.percent = 50; job.status = t('opera.status_converting_video');
      const ts = Date.now();
      const mimeSubtype = meta.mimetype ? meta.mimetype.split('/')[1] : 'bin';
      const tempIn  = safeTempPath(`video_${ts}.${mimeSubtype}`);
      const tempOut = safeTempPath(`video_${ts}.mp4`);
      try {
        await fs.promises.writeFile(tempIn, mediaBuffer); mediaBuffer = null;
        await new Promise((resolve, reject) => {
          const proc = spawn(ffmpeg, ['-y', '-i', tempIn, '-vf', 'scale=-2:720', '-c:v', 'libx264', '-preset', 'ultrafast', '-crf', '28', '-c:a', 'aac', '-b:a', '96k', '-ar', '44100', '-ac', '2', '-movflags', '+faststart', '-pix_fmt', 'yuv420p', tempOut]);
          let stderr = '';
          proc.stderr.on('data', (d) => { stderr += d.toString(); });
          proc.on('close', (code) => code === 0 ? resolve() : reject(new Error(`FFmpeg video: ${stderr.slice(-200)}`)));
          proc.on('error', reject);
        });
        job.percent = 80; job.status = t('opera.status_sending_video');
        const mp4Buffer = await fs.promises.readFile(tempOut);
        console.log(`[Upload] Job ${jobId}: video converted ${mp4Buffer.length} bytes`);
        await sock.sendMessage(formattedJid, { video: mp4Buffer, caption: caption || undefined, mimetype: 'video/mp4' });
      } catch (convErr) {
        console.error(`[Upload] Job ${jobId}: video conv failed:`, convErr);
        job.percent = 80; job.status = t('opera.status_conv_failed');
        const fallback = mediaBuffer || await fs.promises.readFile(meta.path);
        await sock.sendMessage(formattedJid, { document: fallback, mimetype: meta.mimetype, fileName: meta.originalname });
      } finally {
        fs.promises.unlink(tempIn).catch(() => {});
        fs.promises.unlink(tempOut).catch(() => {});
      }
    }
    else {
      job.percent = 65; job.status = t('opera.status_sending_doc');
      await sock.sendMessage(formattedJid, { document: mediaBuffer, mimetype: meta.mimetype, fileName: meta.originalname });
    }

    // Cleanup on success
    if (meta._fromCache) {
      uploadFileCache.delete(to);
      fs.promises.unlink(meta.path).catch(() => {});
    } else {
      fs.promises.unlink(meta.path).catch(() => {});
      const oldCached = uploadFileCache.get(to);
      if (oldCached) { fs.promises.unlink(oldCached.path).catch(() => {}); uploadFileCache.delete(to); }
    }

    job.percent = 100;
    job.status = `${job.typeLabel} ${t('opera.sent_to')} ${job.contactName}`;
    job.done = true;

  } catch (error) {
    console.error(`[Upload] Job ${jobId}: error:`, error);
    // Cache file for retry on single-request uploads (not chunked)
    if (meta?.path && !meta._fromCache && !meta._fromChunk && fs.existsSync(meta.path)) {
      const oldCached = uploadFileCache.get(to);
      if (oldCached && oldCached.path !== meta.path) fs.promises.unlink(oldCached.path).catch(() => {});
      uploadFileCache.set(to, { path: meta.path, originalname: meta.originalname, mimetype: meta.mimetype, size: meta.size, timestamp: Date.now() });
      setTimeout(() => {
        const c = uploadFileCache.get(to);
        if (c && c.path === meta.path) { uploadFileCache.delete(to); fs.promises.unlink(meta.path).catch(() => {}); }
      }, 30 * 60 * 1000);
    } else if (meta?.path && meta._fromChunk) {
      fs.promises.unlink(meta.path).catch(() => {});
    }
    const j = uploadJobs.get(jobId);
    if (j) { j.percent = 0; j.status = `${t('opera.send_failed')} ${error.message}`; j.done = true; j.error = error.message; }
  }
}

app.post("/opera/upload", (req, res) => {
  req.setTimeout(300000);
  res.setTimeout(300000);

  // === DEBUG: log everything about the incoming request ===
  console.log('[Upload DEBUG] === NEW UPLOAD REQUEST ===');
  console.log('[Upload DEBUG] Content-Type:', req.headers['content-type']);
  console.log('[Upload DEBUG] Content-Length:', req.headers['content-length']);
  console.log('[Upload DEBUG] User-Agent:', req.headers['user-agent']);
  console.log('[Upload DEBUG] All headers:', JSON.stringify(req.headers, null, 2));

  let bb;
  try {
    bb = Busboy({ headers: req.headers, limits: { fileSize: 64 * 1024 * 1024 + 1, files: 1, fields: 20 } });
  } catch (e) {
    console.log('[Upload DEBUG] Busboy init FAILED:', e.message);
    return res.send(operaResultPage(t('common.error'), t('opera.invalid_request'), null));
  }
  console.log('[Upload DEBUG] Busboy initialized OK');

  const fields = {};
  let jobId = null;
  let responseSent = false;
  let fileMeta = null;
  let fileEventFired = false;

  // fileReady resolves when the file has been fully written to disk
  let fileReadyResolve, fileReadyReject;
  const fileReady = new Promise((res, rej) => { fileReadyResolve = res; fileReadyReject = rej; });

  function sendOnce(code, data) {
    if (responseSent) return;
    responseSent = true;
    if (code === 303) {
      // XHTML Mobile Profile browsers often don't handle 303 redirects properly —
      // they fail to follow the Location header and try to render Express's default
      // redirect HTML body, which is not valid XHTML-MP, causing "unknown file format".
      // Instead, serve a proper XHTML-MP page with meta refresh to navigate to the status URL.
      if (UPLOAD_MARKUP_MODE === 'xhtml') {
        res.setHeader("Content-Type", "text/html; charset=utf-8");
        res.setHeader("Cache-Control", "no-cache, no-store, must-revalidate");
        const escUrl = data.replace(/&/g, '&amp;').replace(/"/g, '&quot;');
        res.send(`<!DOCTYPE html PUBLIC "-//WAPFORUM//DTD XHTML Mobile 1.0//EN" "http://www.wapforum.org/DTD/xhtml-mobile10.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=utf-8"/>
<meta http-equiv="refresh" content="0;url=${escUrl}"/>
<title>${t('opera.sending_title')}</title>
<style type="text/css">${XHTML_CSS}</style>
</head>
<body>
<div class="wa-bar">${t('opera.sending_title')}</div>
<p>${t('opera.status_uploading')}...</p>
<p><a href="${escUrl}">${t('opera.refresh_now')}</a></p>
</body>
</html>`);
      } else {
        authRedirect(res, data, 303);
      }
    }
    else {
      res.setHeader("Content-Type", "text/html; charset=utf-8");
      res.send(data);
    }
  }

  bb.on('field', (name, val) => {
    console.log(`[Upload DEBUG] Field: "${name}" = "${val}"`);
    fields[name] = val;
  });

  bb.on('file', (_fieldname, file, info) => {
    fileEventFired = true;
    console.log(`[Upload DEBUG] FILE EVENT FIRED! fieldname="${_fieldname}", filename="${info.filename}", mimeType="${info.mimeType}"`);
    let fileBytes = 0;
    file.on('data', (chunk) => { fileBytes += chunk.length; });
    file.on('end', () => { console.log(`[Upload DEBUG] File stream ended, total bytes: ${fileBytes}`); });
    const { filename, mimeType } = info;
    const to = fields.to || fields.jid;
    const type = fields.type || 'document';

    if (!to) {
      file.resume();
      fileReadyResolve(null);
      return sendOnce(200, operaResultPage(t('common.error'), t('opera.no_recipient2'), null));
    }
    if (!sock) {
      file.resume();
      fileReadyResolve(null);
      return sendOnce(200, operaResultPage(t('opera.disconnected'), t('opera.not_connected'), null));
    }

    // Register job
    jobId = `${Date.now()}-${crypto.randomBytes(4).toString('hex')}`;
    const contact = contactStore.get(to);
    const contactName = contact?.name || contact?.notify || to.split('@')[0];
    const typeLabel = t(TYPE_LABEL_KEYS.get(type) || 'opera.type_media');
    uploadJobs.set(jobId, {
      percent: 5, status: t('opera.status_uploading'), jid: to, contactName, type, typeLabel, done: false, error: null
    });
    setTimeout(() => uploadJobs.delete(jobId), 30 * 60 * 1000);

    // XHTML browsers close the upload connection when they receive a response,
    // so we must NOT send the redirect until the file is fully received.
    // Modern browsers (HTML5) keep streaming in background after getting the 303.
    const isXhtml = fields.xhtml === '1';
    if (!isXhtml) {
      sendOnce(303, `/opera/upload-status?id=${jobId}`);
    }

    // Save file to disk while upload continues
    const tempPath = safeTempPath(`upload_${jobId}`);
    let fileSize = 0;
    let limitHit = false;
    file.on('limit', () => { limitHit = true; });
    file.on('data', (chunk) => { fileSize += chunk.length; });
    const ws = fs.createWriteStream(tempPath);
    file.pipe(ws);
    ws.on('finish', () => {
      fileMeta = { path: tempPath, originalname: filename || 'file', mimetype: mimeType || 'application/octet-stream', size: fileSize, limitHit };
      // For XHTML: now that file is fully received, redirect to status page
      if (isXhtml) {
        sendOnce(303, `/opera/upload-status?id=${jobId}&xhtml=1`);
      }
      fileReadyResolve(fileMeta);
    });
    ws.on('error', (err) => fileReadyReject(err));
    file.on('error', (err) => fileReadyReject(err));
  });

  bb.on('finish', async () => {
    console.log('[Upload DEBUG] BUSBOY FINISH event fired');
    console.log('[Upload DEBUG] fileEventFired:', fileEventFired);
    console.log('[Upload DEBUG] jobId:', jobId);
    console.log('[Upload DEBUG] All fields received:', JSON.stringify(fields));

    const to = fields.to || fields.jid;
    const type = fields.type || 'document';
    const caption = fields.caption;
    const useCached = fields.useCached === '1';

    // Case: useCached — no file event fires, use cached file
    if (!jobId) {
      console.log('[Upload DEBUG] jobId is NULL => file event never set it. useCached:', useCached, 'to:', to);
      if (useCached && to) {
        const cached = uploadFileCache.get(to);
        if (cached && fs.existsSync(cached.path)) {
          jobId = `${Date.now()}-${crypto.randomBytes(4).toString('hex')}`;
          const contact = contactStore.get(to);
          const contactName = contact?.name || contact?.notify || to.split('@')[0];
          const typeLabel = t(TYPE_LABEL_KEYS.get(type) || 'opera.type_media');
          uploadJobs.set(jobId, { percent: 10, status: t('opera.status_fetching'), jid: to, contactName, type, typeLabel, done: false, error: null });
          setTimeout(() => uploadJobs.delete(jobId), 30 * 60 * 1000);
          const xhtmlFlag = fields.xhtml === '1' ? '&xhtml=1' : '';
          sendOnce(303, `/opera/upload-status?id=${jobId}${xhtmlFlag}`);
          fileMeta = { path: cached.path, originalname: cached.originalname, mimetype: cached.mimetype, size: cached.size, _fromCache: true };
          fileReadyResolve(fileMeta);
        } else {
          fileReadyResolve(null);
          return sendOnce(200, operaResultPage(t('common.error'), t('opera.no_cache'), to));
        }
      } else {
        fileReadyResolve(null);
        return sendOnce(200, operaResultPage(t('common.error'), t('opera.no_file'), to || null));
      }
    }

    // Wait for file to finish writing to disk
    let meta;
    try { meta = await fileReady; } catch (err) {
      console.error('[Upload busboy] File write error:', err);
      const j = uploadJobs.get(jobId);
      if (j) { j.percent = 0; j.status = `${t('opera.file_receive_error')} ${err.message}`; j.done = true; j.error = err.message; }
      return;
    }
    if (!meta) return;

    const job = uploadJobs.get(jobId);
    if (!job) return;

    // Validate
    if (!meta._fromCache && meta.size === 0) {
      fs.promises.unlink(meta.path).catch(() => {});
      job.percent = 0; job.status = t('opera.empty_file'); job.done = true; job.error = 'empty';
      return;
    }
    if (meta.limitHit) {
      fs.promises.unlink(meta.path).catch(() => {});
      const maxMB = Math.round((WA_UPLOAD_SIZE_LIMITS[type] || WA_UPLOAD_SIZE_LIMITS.document) / (1024 * 1024));
      job.percent = 0; job.status = `${t('opera.file_too_large_type')} ${type}: ${maxMB} ${t('opera.size_limit')}`; job.done = true; job.error = 'size';
      return;
    }
    const maxSize = WA_UPLOAD_SIZE_LIMITS[type] || WA_UPLOAD_SIZE_LIMITS.document;
    if (meta.size > maxSize) {
      if (!meta._fromCache) fs.promises.unlink(meta.path).catch(() => {});
      const maxMB = Math.round(maxSize / (1024 * 1024));
      const fileMB = (meta.size / (1024 * 1024)).toFixed(1);
      job.percent = 0; job.status = `${t('opera.file_too_large_size')} (${fileMB} MB). ${t('opera.limit')} ${maxMB} MB.`; job.done = true; job.error = 'size';
      return;
    }

    await processUploadJob(jobId, meta, to, type, caption);
  });

  bb.on('error', (err) => {
    console.error('[Upload busboy] Parse error:', err);
    fileReadyResolve(null);
    // Update job status if a job was already created
    if (jobId) {
      const j = uploadJobs.get(jobId);
      if (j) { j.percent = 0; j.status = `${t('opera.file_error')}: ${err.message}`; j.done = true; j.error = err.message; }
    }
    if (!responseSent) {
      res.setHeader("Content-Type", UPLOAD_MARKUP_MODE === 'xhtml' ? "text/html; charset=utf-8" : "text/html; charset=utf-8");
    }
    sendOnce(200, operaResultPage(t('common.error'), t('opera.file_error'), fields.to || fields.jid || null));
  });

  req.on('error', (err) => {
    console.error('[Upload] Request stream error:', err);
    fileReadyResolve(null);
    if (jobId) {
      const j = uploadJobs.get(jobId);
      if (j) { j.percent = 0; j.status = `Connection error: ${err.message}`; j.done = true; j.error = err.message; }
    }
  });

  req.on('aborted', () => {
    console.warn('[Upload] Request aborted by client');
    fileReadyResolve(null);
    if (jobId) {
      const j = uploadJobs.get(jobId);
      if (j && !j.done) { j.percent = 0; j.status = t('opera.file_error'); j.done = true; j.error = 'aborted'; }
    }
  });

  // Some XHTML/WAP browsers omit the closing multipart boundary (--boundary--),
  // causing busboy to throw "Unexpected end of form". We manually feed data to busboy
  // and append the closing boundary if the browser didn't send it.
  const ctBoundary = (req.headers['content-type'] || '').match(/boundary=(?:"([^"]+)"|([^\s;]+))/);
  if (ctBoundary) {
    const boundary = ctBoundary[1] || ctBoundary[2];
    const closingSeq = Buffer.from(`\r\n--${boundary}--`);
    const tailLen = closingSeq.length + 4;
    let tail = Buffer.alloc(0);

    // Detect Kannel WAP gateway — needs multipart fixups (LF→CRLF, doubled quotes)
    const isKannel = /kannel/i.test(req.headers['x-wap-gateway'] || '') || /kannel/i.test(req.headers['via'] || '');

    let totalDataBytes = 0;
    let firstChunkLogged = false;
    req.on('data', (chunk) => {
      totalDataBytes += chunk.length;

      if (!firstChunkLogged) {
        firstChunkLogged = true;
        console.log('[Upload DEBUG] First chunk raw (500 bytes):', chunk.slice(0, 500).toString('latin1'));
        // Hex dump for line-ending diagnosis
        const hexSample = chunk.slice(0, 200).toString('hex').match(/.{1,2}/g).join(' ');
        console.log('[Upload DEBUG] First 200 bytes HEX:', hexSample);
      }

      if (isKannel) {
        // Kannel WAP gateway sends malformed multipart data:
        // 1) doubled trailing quotes in Content-Disposition: name="field""
        // 2) LF-only line endings instead of CRLF (which busboy/dicer requires)
        // Using latin1 preserves all byte values so binary file data is not corrupted.
        let chunkStr = chunk.toString('latin1');

        // Fix: split on boundary, fix headers in each part, rejoin.
        const boundaryLine = '--' + boundary;
        const parts = chunkStr.split(boundaryLine);
        chunkStr = parts.map((part, i) => {
          if (i === 0 && part.trim() === '') return part; // preamble
          // Find end of headers: \r\n\r\n or \n\n
          const hdrEnd2 = part.indexOf('\n\n');
          const hdrEnd4 = part.indexOf('\r\n\r\n');
          let hdrEnd, hdrSep;
          if (hdrEnd4 >= 0 && (hdrEnd4 <= hdrEnd2 || hdrEnd2 < 0)) {
            hdrEnd = hdrEnd4; hdrSep = '\r\n\r\n';
          } else if (hdrEnd2 >= 0) {
            hdrEnd = hdrEnd2; hdrSep = '\n\n';
          } else {
            return part; // no header/body separator found, leave as-is
          }
          let headers = part.substring(0, hdrEnd);
          const body = part.substring(hdrEnd + hdrSep.length);
          // Normalize line endings in headers to CRLF
          headers = headers.replace(/\r\n/g, '\n').replace(/\n/g, '\r\n');
          // Fix doubled trailing quotes in Content-Disposition (may occur multiple times)
          // Kannel doubles every closing quote: name="field"" filename="img.jpg""
          while (headers.includes('""')) {
            headers = headers.replace(/""/g, '"');
          }
          // Kannel/Nokia may send file parts without filename= in Content-Disposition,
          // or even without Content-Disposition at all. Busboy only fires the 'file'
          // event when filename= is present, so we must inject one.
          const ctMatch = headers.match(/Content-Type:\s*([^\r\n]+)/i);
          if (ctMatch) {
            const partCt = ctMatch[1].trim().toLowerCase();
            const isFilePart = partCt && !partCt.startsWith('text/plain');
            if (isFilePart) {
              const hasDisposition = /Content-Disposition:/i.test(headers);
              const hasFilename = /filename=/i.test(headers);
              console.log(`[Upload DEBUG] Kannel file part: ct=${partCt} hasDisposition=${hasDisposition} hasFilename=${hasFilename}`);
              if (!hasDisposition) {
                // No Content-Disposition at all — add one with name and filename
                const ext = { 'image/jpeg': '.jpg', 'image/png': '.png', 'image/gif': '.gif',
                  'image/bmp': '.bmp', 'audio/midi': '.mid', 'audio/mid': '.mid',
                  'video/3gpp': '.3gp', 'application/java-archive': '.jar' }[partCt] || '';
                headers += `\r\nContent-Disposition: form-data; name="media"; filename="upload${ext}"`;
              } else if (!hasFilename) {
                
                // Has Content-Disposition but no filename= — inject filename
                const ext = { 'image/jpeg': '.jpg', 'image/png': '.png', 'image/gif': '.gif',
                  'image/bmp': '.bmp', 'audio/midi': '.mid', 'audio/mid': '.mid',
                  'video/3gpp': '.3gp', 'application/java-archive': '.jar' }[partCt] || '';
                headers = headers.replace(
                  /(Content-Disposition:[^\r\n]*)/i,
                  `$1; filename="upload${ext}"`
                );
              }
            }
          }
          return headers + '\r\n\r\n' + body;
        }).join(boundaryLine);

        // Fix bare LF before boundary delimiters → CRLF (busboy/dicer requires \r\n--boundary)
        // Kannel sends \n--boundary but the multipart spec mandates \r\n--boundary.
        chunkStr = chunkStr.split('\r\n' + boundaryLine).join('\n' + boundaryLine);
        chunkStr = chunkStr.split('\n' + boundaryLine).join('\r\n' + boundaryLine);

        const fixedBuf = Buffer.from(chunkStr, 'latin1');
        console.log('[Upload DEBUG] Fixed first 500 bytes:', fixedBuf.subarray(0, 500).toString('latin1'));
        bb.write(fixedBuf);
      } else {
        bb.write(chunk);
      }
      // Keep only the last N bytes to check for closing boundary at the end
      tail = Buffer.concat([tail, chunk]);
      if (tail.length > tailLen) tail = tail.slice(-tailLen);
    });
    req.on('end', () => {
      console.log('[Upload DEBUG] Request stream ended. Total bytes received:', totalDataBytes);
      if (!tail.includes(closingSeq)) {
        console.log('[Upload DEBUG] Closing multipart boundary missing — injecting it');
        bb.write(closingSeq);
        bb.write(Buffer.from('\r\n'));
      }
      bb.end();
    });
    req.on('error', (err) => bb.destroy(err));
  } else {
    req.pipe(bb);
  }
});

// ---- Chunked parallel upload endpoint ----
// Each chunk is a separate POST with FormData fields:
//   uploadId, chunkIndex, totalChunks, to, type, caption, filename, mimetype, filesize, chunk(binary)
// The server saves each chunk to disk and, when all arrive, assembles + calls processUploadJob.
// Client navigates to /opera/upload-status?id=<uploadId> immediately after starting the first XHR.
app.post("/opera/upload-chunk", (req, res) => {
  req.setTimeout(120000);

  let bb;
  try {
    bb = Busboy({ headers: req.headers, limits: { fileSize: 4 * 1024 * 1024, files: 1, fields: 20 } });
  } catch (e) {
    return res.status(400).json({ error: 'Invalid Content-Type' });
  }

  const fields = {};
  const chunkBuffers = [];

  bb.on('field', (name, val) => { fields[name] = val; });

  bb.on('file', (_name, file) => {
    file.on('data', (d) => chunkBuffers.push(d));
    file.on('error', (err) => console.error('[Chunk] file stream error:', err));
  });

  bb.on('finish', async () => {
    const { uploadId, chunkIndex, totalChunks, to, type, caption, filename, mimetype, filesize } = fields;
    const idx   = parseInt(chunkIndex,  10);
    const total = parseInt(totalChunks, 10);
    const chunkData = Buffer.concat(chunkBuffers);

    if (!uploadId || isNaN(idx) || isNaN(total) || !to || chunkData.length === 0) {
      return res.status(400).json({ error: 'Missing fields or empty chunk' });
    }
    if (!sock) return res.status(503).json({ error: 'WhatsApp disconnesso' });

    // Save chunk to disk
    const chunkDir  = safeTempPath(`chunks/${uploadId}`);
    fs.mkdirSync(chunkDir, { recursive: true });
    const chunkPath = path.join(chunkDir, `chunk_${idx}`);
    try {
      await fs.promises.writeFile(chunkPath, chunkData);
    } catch (e) {
      return res.status(500).json({ error: 'Disk write failed' });
    }

    // Register session + job on first chunk received
    let session = chunkSessions.get(uploadId);
    if (!session) {
      const contact   = contactStore.get(to);
      const contactName = contact?.name || contact?.notify || to.split('@')[0];
      const typeLabel = t(TYPE_LABEL_KEYS.get(type) || 'opera.type_media');
      uploadJobs.set(uploadId, {
        percent: 5, status: t('opera.status_uploading_chunks'), jid: to,
        contactName, type, typeLabel, done: false, error: null
      });
      setTimeout(() => uploadJobs.delete(uploadId), 30 * 60 * 1000);
      session = { received: new Set(), total, to, type, caption: caption || '', filename: filename || 'file', mimetype: mimetype || 'application/octet-stream', filesize: parseInt(filesize, 10) || 0, chunkDir, processed: false };
      chunkSessions.set(uploadId, session);
      setTimeout(() => {
        chunkSessions.delete(uploadId);
        fs.promises.rm(chunkDir, { recursive: true, force: true }).catch(() => {});
      }, 30 * 60 * 1000);
    }

    session.received.add(idx);

    // Update upload progress (5% → 40% during chunk upload phase)
    const job = uploadJobs.get(uploadId);
    if (job && !job.done) {
      const pct = Math.round((session.received.size / session.total) * 35) + 5;
      job.percent = pct;
      job.status  = `${t('opera.loading_chunks')} ${session.received.size}/${session.total} ${t('opera.chunks')}...`;
    }

    res.json({ received: session.received.size, total: session.total, percent: job?.percent ?? 5 });

    // All chunks arrived — assemble and process
    if (session.received.size === session.total && !session.processed) {
      session.processed = true;

      // Assemble in background
      ;(async () => {
        const j = uploadJobs.get(uploadId);
        if (j) { j.percent = 40; j.status = t('opera.status_assembling'); }

        try {
          const assembledPath = safeTempPath(`assembled_${uploadId}`);
          const ws = fs.createWriteStream(assembledPath);
          for (let i = 0; i < session.total; i++) {
            const cp = path.join(session.chunkDir, `chunk_${i}`);
            const buf = await fs.promises.readFile(cp);
            ws.write(buf);
            fs.promises.unlink(cp).catch(() => {});
          }
          await new Promise((resolve, reject) => { ws.end(); ws.on('finish', resolve); ws.on('error', reject); });
          fs.promises.rm(session.chunkDir, { recursive: true, force: true }).catch(() => {});

          const meta = { path: assembledPath, originalname: session.filename, mimetype: session.mimetype, size: session.filesize || (await fs.promises.stat(assembledPath)).size, _fromChunk: true };
          await processUploadJob(uploadId, meta, session.to, session.type, session.caption);
        } catch (err) {
          console.error('[Chunk] Assembly/process error:', err);
          const j = uploadJobs.get(uploadId);
          if (j) { j.percent = 0; j.status = `${t('common.error')}: ${err.message}`; j.done = true; j.error = err.message; }
        }
      })();
    }
  });

  bb.on('error', (err) => {
    console.error('[Chunk] Busboy error:', err);
    res.status(500).json({ error: 'Parse error' });
  });

  req.pipe(bb);
});

// SSR upload progress page — auto-refreshes every 4s via HTTP Refresh header + meta tag.
app.get("/opera/upload-status", (req, res) => {
  const jobId = req.query.id;

  if (!jobId || !uploadJobs.has(jobId)) {
    return res.send(operaResultPage(t('common.error'), t('opera.upload_not_found'), null));
  }

  const job = uploadJobs.get(jobId);

  // Job complete — redirect to final result page (no more auto-refresh)
  // Do NOT delete job: Opera Mini proxy may issue duplicate requests.
  if (job.done) {
    // WML/XHTML mode — serve result via sendWml() pipeline
    if (UPLOAD_MARKUP_MODE !== 'html5') {
      const title = job.error ? t('common.error') : t('opera.sent');
      const statusMsg = esc(job.status);
      const jid = job.jid;
      const body = `
        <p><b>${title}</b></p>
        <p>${statusMsg}</p>
        ${jid ? `<p><a href="/opera/send?jid=${encodeURIComponent(jid)}">${t('opera.send_more')}</a></p>
        <p><a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}">${t('opera.back_to_chat')}</a></p>` : ''}
        <p><a href="/wml/home.wml">${t('common.home')}</a></p>`;
      return sendWml(res, card("upload-result", title, body), "", UPLOAD_MARKUP_MODE);
    }
    res.setHeader("Content-Type", "text/html; charset=utf-8");
    res.setHeader("Cache-Control", "no-cache, no-store, must-revalidate");
    res.setHeader("Pragma", "no-cache");
    res.setHeader("Expires", "0");
    if (job.error) return res.send(operaResultPage(t('common.error'), job.status, job.jid));
    return res.send(operaResultPage(t('opera.sent'), job.status, job.jid));
  }

  const pct = job.percent;
  const escapedStatus = job.status.replace(/</g, '&lt;').replace(/>/g, '&gt;');
  const escapedName = job.contactName.replace(/</g, '&lt;').replace(/>/g, '&gt;');

  // WML / XHTML mode — use sendWml() pipeline for consistent rendering
  if (UPLOAD_MARKUP_MODE !== 'html5') {
    const phaseLabel = pct < 20 ? t('opera.phase_receiving') : pct < 50 ? t('opera.phase_processing') : pct < 85 ? t('opera.phase_sending') : t('opera.phase_finishing');
    const bar = '[' + '#'.repeat(Math.round(pct / 5)) + '.'.repeat(20 - Math.round(pct / 5)) + ']';
    const refreshUrl = `/opera/upload-status?id=${encodeURIComponent(jobId)}`;
    const body = `
      <p><b>${t('opera.sending_title')} ${job.typeLabel}</b></p>
      <p>${t('opera.to')} ${escapedName}</p>
      <p>${phaseLabel}</p>
      <p><b>${bar} ${pct}%</b></p>
      <p>${escapedStatus}</p>
      <p><a href="${refreshUrl}">${t('opera.refresh_now')}</a></p>`;
    return sendWml(res, card("upload-progress", t('opera.sending_title'), body, refreshUrl), "", UPLOAD_MARKUP_MODE);
  }

  // Phase (0=upload 1=processing 2=sending 3=finishing)
  const phase = pct < 20 ? 0 : pct < 50 ? 1 : pct < 85 ? 2 : 3;
  const phaseNames  = [t('opera.phase_receiving'), t('opera.phase_processing'), t('opera.phase_sending'), t('opera.phase_finishing')];
  const phaseSubs   = [t('opera.phase_sub_receiving'), t('opera.phase_sub_processing'), t('opera.phase_sub_sending'), t('opera.phase_sub_finishing')];
  const phaseColors = ['#25d366', '#e67e22', '#2980b9', '#25d366'];

  // Inline SVG icons (Feather-style, stroke-based)
  const SVG_UPLOAD = `<svg width="36" height="36" viewBox="0 0 24 24" fill="none" stroke="${phaseColors[0]}" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="16 16 12 12 8 16"/><line x1="12" y1="12" x2="12" y2="21"/><path d="M20.39 18.39A5 5 0 0 0 18 9h-1.26A8 8 0 1 0 3 16.3"/></svg>`;
  const SVG_GEAR   = `<svg width="36" height="36" viewBox="0 0 24 24" fill="none" stroke="${phaseColors[1]}" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="3"/><path d="M19.4 15a1.65 1.65 0 0 0 .33 1.82l.06.06a2 2 0 0 1-2.83 2.83l-.06-.06a1.65 1.65 0 0 0-1.82-.33 1.65 1.65 0 0 0-1 1.51V21a2 2 0 0 1-4 0v-.09A1.65 1.65 0 0 0 9 19.4a1.65 1.65 0 0 0-1.82.33l-.06.06a2 2 0 0 1-2.83-2.83l.06-.06A1.65 1.65 0 0 0 4.68 15a1.65 1.65 0 0 0-1.51-1H3a2 2 0 0 1 0-4h.09A1.65 1.65 0 0 0 4.6 9a1.65 1.65 0 0 0-.33-1.82l-.06-.06a2 2 0 0 1 2.83-2.83l.06.06A1.65 1.65 0 0 0 9 4.68a1.65 1.65 0 0 0 1-1.51V3a2 2 0 0 1 4 0v.09a1.65 1.65 0 0 0 1 1.51 1.65 1.65 0 0 0 1.82-.33l.06-.06a2 2 0 0 1 2.83 2.83l-.06.06A1.65 1.65 0 0 0 19.4 9a1.65 1.65 0 0 0 1.51 1H21a2 2 0 0 1 0 4h-.09a1.65 1.65 0 0 0-1.51 1z"/></svg>`;
  const SVG_SEND   = `<svg width="36" height="36" viewBox="0 0 24 24" fill="none" stroke="${phaseColors[2]}" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><line x1="22" y1="2" x2="11" y2="13"/><polygon points="22 2 15 22 11 13 2 9 22 2"/></svg>`;
  const SVG_CHECK  = `<svg width="36" height="36" viewBox="0 0 24 24" fill="none" stroke="${phaseColors[3]}" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M22 11.08V12a10 10 0 1 1-5.93-9.14"/><polyline points="22 4 12 14.01 9 11.01"/></svg>`;
  const phaseIcons = [SVG_UPLOAD, SVG_GEAR, SVG_SEND, SVG_CHECK];

  // Step states: [Ricevuto, Elabora, Invio, Fatto]
  const stepClass = [
    pct >= 20 ? 'done' : pct >= 5  ? 'active' : 'wait',
    pct >= 50 ? 'done' : pct >= 20 ? 'active' : 'wait',
    pct >= 85 ? 'done' : pct >= 50 ? 'active' : 'wait',
    pct >= 100? 'done' : pct >= 85 ? 'active' : 'wait',
  ];

  const html = `<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width,initial-scale=1">
  <meta http-equiv="refresh" content="4">
  <title>${t('opera.sending_title')} ${job.typeLabel}...</title>
  ${WAP_FAVICON_LINK}
  <style>
    *{box-sizing:border-box;margin:0;padding:0}
    body{font-family:Arial,sans-serif;background:#e5ddd5;min-height:100vh;font-size:14px}
    .hdr{background:#075e54;color:#fff;padding:12px 16px}
    .hdr-title{font-size:16px;font-weight:700}
    .hdr-sub{font-size:12px;opacity:.8;margin-top:3px}
    .wrap{padding:12px;max-width:420px;margin:0 auto}
    .card{background:#fff;border-radius:10px;padding:18px 16px;margin-bottom:12px;border:1px solid #ddd}
    .phase-tbl{width:100%;border-collapse:collapse;margin-bottom:16px}
    .phase-td-icon{width:52px;vertical-align:middle;text-align:center;padding-right:12px}
    .phase-td-info{vertical-align:middle}
    .phase-name{font-size:15px;font-weight:700;color:#075e54}
    .phase-sub{font-size:12px;color:#888;margin-top:3px}
    .steps-tbl{width:100%;border-collapse:collapse;margin:12px 0}
    .step-td{text-align:center;padding:0 4px}
    .step-dot{width:12px;height:12px;border-radius:50%;margin:0 auto 4px;border:2px solid #ccc;background:#fff}
    .done .step-dot{background:#25d366;border-color:#25d366}
    .active .step-dot{background:#075e54;border-color:#075e54}
    .done .step-lbl{color:#25d366;font-weight:700;font-size:11px}
    .active .step-lbl{color:#075e54;font-weight:700;font-size:11px}
    .wait .step-lbl{color:#bbb;font-size:11px}
    .bar-bg{background:#e0e0e0;border-radius:8px;height:24px;overflow:hidden;margin:12px 0;position:relative}
    .bar-fg{background:#25d366;height:100%;width:${pct}%;border-radius:8px}
    .bar-lbl{position:absolute;top:0;left:0;right:0;bottom:0;text-align:center;line-height:24px;font-size:12px;font-weight:700;color:#fff}
    .status-msg{font-size:13px;color:#555;text-align:center;margin:10px 0 4px}
    .auto-msg{font-size:11px;color:#aaa;text-align:center;margin-top:4px}
    .btn{display:block;background:#25d366;color:#fff;text-align:center;padding:13px;border-radius:8px;font-size:15px;font-weight:700;text-decoration:none;margin-top:4px;border:0}
    .note{font-size:11px;color:#aaa;text-align:center;margin-top:8px}
  </style>
</head>
<body>
  <div class="hdr">
    <div class="hdr-title">${t('opera.sending_title')} ${job.typeLabel}</div>
    <div class="hdr-sub">${t('opera.to')} ${escapedName}</div>
  </div>
  <div class="wrap">
    <div class="card">

      <table class="phase-tbl"><tr>
        <td class="phase-td-icon">${phaseIcons[phase]}</td>
        <td class="phase-td-info">
          <div class="phase-name">${phaseNames[phase]}</div>
          <div class="phase-sub">${phaseSubs[phase]}</div>
        </td>
      </tr></table>

      <table class="steps-tbl"><tr>
        <td class="step-td ${stepClass[0]}"><div class="step-dot"></div><span class="step-lbl">${t('opera.step_received')}</span></td>
        <td class="step-td ${stepClass[1]}"><div class="step-dot"></div><span class="step-lbl">${t('opera.step_processing')}</span></td>
        <td class="step-td ${stepClass[2]}"><div class="step-dot"></div><span class="step-lbl">${t('opera.step_sending')}</span></td>
        <td class="step-td ${stepClass[3]}"><div class="step-dot"></div><span class="step-lbl">${t('opera.step_done')}</span></td>
      </tr></table>

      <div class="bar-bg">
        <div class="bar-fg"></div>
        <div class="bar-lbl">${pct}%</div>
      </div>

      <div class="status-msg">${escapedStatus}</div>
      <div class="auto-msg">${t('opera.auto_refresh')}</div>
    </div>

    <a href="/opera/upload-status?id=${jobId}" class="btn">${t('opera.refresh_now')}</a>
    <div class="note">${t('opera.auto_note')} &bull; ${pct}${t('opera.pct_complete')}</div>
  </div>
</body>
</html>`;

  res.setHeader("Content-Type", "text/html; charset=utf-8");
  res.setHeader("Cache-Control", "no-cache, no-store, must-revalidate");
  res.setHeader("Pragma", "no-cache");
  res.setHeader("Expires", "0");
  res.setHeader("Refresh", "4"); // HTTP-level auto-refresh (more reliable on Opera Mini proxy)
  res.send(html);
});

// Helper function to generate result page
function operaResultPage(title, message, jid) {
  const escapedMessage = String(message || '').replace(/</g, '&lt;').replace(/>/g, '&gt;');
  const isSuccess = title === t('opera.sent');
  const isDisconnected = title === t('opera.disconnected');

  if (UPLOAD_MARKUP_MODE === 'xhtml') {
    const statusClass = isSuccess ? 'cached-section' : 'upload-section';
    return `<!DOCTYPE html PUBLIC "-//WAPFORUM//DTD XHTML Mobile 1.0//EN" "http://www.wapforum.org/DTD/xhtml-mobile10.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
  <meta http-equiv="Content-Type" content="text/html; charset=utf-8"/>
  <meta http-equiv="cache-control" content="no-cache, no-store, must-revalidate"/>
  <meta http-equiv="pragma" content="no-cache"/>
  <meta http-equiv="expires" content="0"/>
  <title>${title}</title>
  <style type="text/css">${XHTML_CSS}</style>
</head>
<body>
  <div class="wa-bar">${title}</div>
  <div class="${statusClass}">
    <p><b>${title}</b></p>
    <p>${escapedMessage}</p>
  </div>
  ${jid ? `<a class="back-link" href="/opera/send?jid=${encodeURIComponent(jid)}">${t('opera.send_more')}</a>
  <a class="back-link" href="/wml/chat.wml?jid=${encodeURIComponent(jid)}">${t('opera.back_to_chat')}</a>` : ''}
  <a class="back-link" href="/wml/home.wml">${t('opera.contact_list')}</a>
</body>
</html>`;
  }

  return `<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta http-equiv="cache-control" content="no-cache, no-store, must-revalidate">
  <meta http-equiv="pragma" content="no-cache">
  <meta http-equiv="expires" content="0">
  <title>${title}</title>
  ${WAP_FAVICON_LINK}
  <style>
    body { font-family: Arial, sans-serif; margin: 8px; font-size: 14px; text-align: center; padding-top: 20px; }
    .result { padding: 20px; margin: 20px 0; }
    .success { background: #dcf8c6; color: #075e54; }
    .error { background: #ffcccb; color: #c00; }
    .disconnected { background: #ffeaa7; color: #d63031; }
    a { color: #075e54; display: block; margin: 10px 0; }
  </style>
</head>
<body>
  <div class="result ${isSuccess ? 'success' : isDisconnected ? 'disconnected' : 'error'}">
    <h1>${title}</h1>
    <p>${escapedMessage}</p>
  </div>
  ${jid ? `<a href="/opera/send?jid=${encodeURIComponent(jid)}">${t('opera.send_more')}</a>
  <a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}">${t('opera.back_to_chat')}</a>` : ''}
  <a href="/wml/home.wml">${t('opera.contact_list')}</a>
</body>
</html>`;
}

// ============ VIDEO FRAME PLAYBACK ENDPOINTS ============

// Serve individual video frame (with WBMP conversion)
app.get("/wml/video-frame/:messageId/:frameNumber", async (req, res) => {
  try {
    const { messageId, frameNumber } = req.params;
    const format = req.query.format || 'wbmp'; // wbmp, jpg, png

    const framesDir = path.join(VIDEO_FRAMES_DIR, messageId);
    const framePath = path.join(framesDir, `frame_${String(frameNumber).padStart(4, '0')}.png`);

    if (!fs.existsSync(framePath)) {
      return res.status(404).send("Frame not found");
    }

    const frameBuffer = await fs.promises.readFile(framePath);

    if (format === 'wbmp') {
      // Convert to WBMP for Nokia compatibility
      const { data: pixels, info } = await sharp(frameBuffer)
        .greyscale()
        .resize(96, 96, { // Smaller for WAP devices
          kernel: sharp.kernel.lanczos3,
          fit: "contain",
          position: "center",
          background: { r: 255, g: 255, b: 255, alpha: 1 },
        })
        .linear(1.3, -30)
        .normalise({ lower: 1, upper: 99 })
        .sharpen({ sigma: 1.5, flat: 2, jagged: 3 })
        .threshold(128, { greyscale: true, grayscale: true })
        .raw()
        .toBuffer({ resolveWithObject: true });

      // Create WBMP header
      const width = info.width;
      const height = info.height;
      const header = Buffer.from([
        0x00, // Type 0
        0x00, // FixHeaderField
        width,
        height,
      ]);

      // Convert pixels to WBMP 1-bit format
      const rowBytes = Math.ceil(width / 8);
      const wbmpData = Buffer.alloc(rowBytes * height);

      for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
          const pixelIndex = y * width + x;
          const pixel = pixels[pixelIndex];
          const isBlack = pixel < 128;

          if (isBlack) {
            const byteIndex = y * rowBytes + Math.floor(x / 8);
            const bitIndex = 7 - (x % 8);
            wbmpData[byteIndex] |= 1 << bitIndex;
          }
        }
      }

      const wbmpBuffer = Buffer.concat([header, wbmpData]);

      res.setHeader("Content-Type", "image/vnd.wap.wbmp");
      res.send(wbmpBuffer);
    } else if (format === 'jpg') {
      const jpegBuffer = await sharp(frameBuffer)
        .resize(128, 128, { fit: "contain", background: { r: 255, g: 255, b: 255 } })
        .jpeg({ quality: 70 })
        .toBuffer();

      res.setHeader("Content-Type", "image/jpeg");
      res.send(jpegBuffer);
    } else {
      res.setHeader("Content-Type", "image/png");
      res.send(frameBuffer);
    }
  } catch (error) {
    logger.error("Video frame error:", error);
    res.status(500).send("Error loading frame");
  }
});

// Video playback WML page with frame-by-frame controls
app.get("/wml/view-video.wml", async (req, res) => {
  try {
    const messageId = req.query.mid || "";
    const jid = req.query.jid || "";
    const frameNum = parseInt(req.query.frame || "1", 10);
    const autoplay = req.query.autoplay === "1";
    const format = req.query.format || "wbmp"; // wbmp, jpg, png

    // O(1) lookup via messageStore instead of O(n) .find()
    const targetMessage = messageStore.get(messageId) || null;

    if (!targetMessage || !targetMessage.message?.videoMessage) {
      return sendWml(
        res,
        resultCard("Error", ["Video message not found"], "/wml/chats.wml")
      );
    }

    const contact = contactStore.get(jid);
    const chatName = contact?.name || contact?.notify || jidFriendly(jid);

    const esc = (text) =>
      (text || "")
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;");

    // Check if frames exist, if not extract them
    const framesDir = path.join(VIDEO_FRAMES_DIR, messageId);
    let frameCount = 0;

    if (fs.existsSync(framesDir)) {
      const frames = fs.readdirSync(framesDir).filter(f => f.endsWith('.png'));
      frameCount = frames.length;
    }

    if (frameCount === 0) {
      // Need to extract frames
      try {
        const mediaData = await downloadMediaMessage(
          targetMessage,
          "buffer",
          {},
          {
            logger,
            reuploadRequest: sock.updateMediaMessage,
          }
        );

        const result = await extractVideoFrames(mediaData, messageId);
        frameCount = result.frameCount;
      } catch (error) {
        logger.error("Frame extraction error:", error);
        return sendWml(
          res,
          resultCard(
            "Error",
            ["Failed to extract video frames", error.message],
            `/wml/media-info.wml?mid=${encodeURIComponent(messageId)}&jid=${encodeURIComponent(jid)}`
          )
        );
      }
    }

    const currentFrame = Math.max(1, Math.min(frameNum, frameCount));
    const vid = targetMessage.message.videoMessage;
    const duration = vid.seconds || 0;

    // Navigation with format parameter
    const prevFrame = currentFrame > 1 ? currentFrame - 1 : frameCount;
    const nextFrame = currentFrame < frameCount ? currentFrame + 1 : 1;

    const prevLink = `/wml/view-video.wml?mid=${encodeURIComponent(messageId)}&amp;jid=${encodeURIComponent(jid)}&amp;frame=${prevFrame}&amp;format=${format}`;
    const nextLink = `/wml/view-video.wml?mid=${encodeURIComponent(messageId)}&amp;jid=${encodeURIComponent(jid)}&amp;frame=${nextFrame}&amp;format=${format}`;
    const autoplayLink = `/wml/view-video.wml?mid=${encodeURIComponent(messageId)}&amp;jid=${encodeURIComponent(jid)}&amp;frame=${nextFrame}&amp;autoplay=1&amp;format=${format}`;

    // WAP only supports WBMP inline - force WBMP for display
    const displayFormat = 'wbmp';

    const body = `<p><b>Video Playback</b></p>
<p>From: ${esc(chatName)}</p>
<p>Frame ${currentFrame}/${frameCount}</p>
<p>Duration: ${duration}s (1 FPS)</p>

<p align="center">
  <img src="/wml/video-frame/${encodeURIComponent(messageId)}/${currentFrame}?format=wbmp" alt="Frame ${currentFrame}"/>
</p>

<p>
  <a href="${prevLink}" accesskey="4">[4] Prev</a> |
  <a href="${nextLink}" accesskey="6">[6] Next</a>
</p>
<p>
  <a href="${autoplayLink}" accesskey="5">[5] ${autoplay ? 'Playing...' : 'Play'}</a>
</p>

<p><b>Download Frame:</b></p>
<p>
  <a href="/wml/video-frame/${encodeURIComponent(messageId)}/${currentFrame}?format=jpg" accesskey="7">[7] JPG</a>
  <a href="/wml/video-frame/${encodeURIComponent(messageId)}/${currentFrame}?format=png" accesskey="8">[8] PNG</a>
</p>

<p>
  <a href="/wml/media-info.wml?mid=${encodeURIComponent(messageId)}&amp;jid=${encodeURIComponent(jid)}" accesskey="0">[0] Back</a>
</p>

${autoplay ? `<onevent type="ontimer"><go href="${nextLink}&amp;autoplay=1"/></onevent><timer value="10"/>` : ''}

<do type="prev" label="${t('common.prev')}">
  <go href="${prevLink}"/>
</do>
<do type="accept" label="${t('common.next')}">
  <go href="${nextLink}"/>
</do>`;

    const wmlOutput = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
<head><meta http-equiv="Cache-Control" content="no-cache"/></head>
<card id="video" title="Video">
${body}
</card>
</wml>`;

    sendRawWmlAware(res, wmlOutput);
  } catch (error) {
    logger.error("Video playback error:", error);
    res.status(500).send("Error loading video");
  }
});

// Video format selection page
app.get("/wml/video-format.wml", async (req, res) => {
  try {
    const messageId = req.query.mid || "";
    const jid = req.query.jid || "";
    const frame = req.query.frame || "1";

    const esc = (text) =>
      (text || "")
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;");

    const body = `<p><b>Select Video Format</b></p>
<p>Choose format for frame display:</p>

<p><b>1. WBMP (B&amp;W)</b></p>
<p>Best for old Nokia devices<br/>
96x96 pixels, 1-bit<br/>
Smallest size, fastest</p>
<p><a href="/wml/view-video.wml?mid=${encodeURIComponent(messageId)}&amp;jid=${encodeURIComponent(jid)}&amp;frame=${frame}&amp;format=wbmp" accesskey="1">[1] Select WBMP</a></p>

<p><b>2. JPEG (Color)</b></p>
<p>Color support<br/>
128x128 pixels<br/>
Medium size</p>
<p><a href="/wml/view-video.wml?mid=${encodeURIComponent(messageId)}&amp;jid=${encodeURIComponent(jid)}&amp;frame=${frame}&amp;format=jpg" accesskey="2">[2] Select JPEG</a></p>

<p><b>3. PNG (Color)</b></p>
<p>High quality color<br/>
128x128 pixels<br/>
Larger size</p>
<p><a href="/wml/view-video.wml?mid=${encodeURIComponent(messageId)}&amp;jid=${encodeURIComponent(jid)}&amp;frame=${frame}&amp;format=png" accesskey="3">[3] Select PNG</a></p>

<p><a href="/wml/view-video.wml?mid=${encodeURIComponent(messageId)}&amp;jid=${encodeURIComponent(jid)}&amp;frame=${frame}" accesskey="0">[0] Back</a></p>

<do type="accept" label="${t('common.back')}">
  <go href="/wml/view-video.wml?mid=${encodeURIComponent(messageId)}&amp;jid=${encodeURIComponent(jid)}&amp;frame=${frame}"/>
</do>`;

    const wmlOutput = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
<head><meta http-equiv="Cache-Control" content="no-cache"/></head>
<card id="format" title="Format">
${body}
</card>
</wml>`;

    sendRawWmlAware(res, wmlOutput);
  } catch (error) {
    logger.error("Video format selection error:", error);
    res.status(500).send("Error loading format selection");
  }
});

// Image format selection page
app.get("/wml/image-format.wml", async (req, res) => {
  try {
    const messageId = req.query.mid || "";
    const jid = req.query.jid || "";

    const esc = (text) =>
      (text || "")
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;");

    const body = `<p><b>Select Image Format</b></p>
<p>Choose format for image display:</p>

<p><b>1. WBMP (B&amp;W)</b></p>
<p>Best for old Nokia devices<br/>
Black &amp; white<br/>
Smallest size, fastest</p>
<p><a href="/wml/view-image.wml?mid=${encodeURIComponent(messageId)}&amp;jid=${encodeURIComponent(jid)}&amp;format=wbmp" accesskey="1">[1] Select WBMP</a></p>

<p><b>2. JPEG (Color)</b></p>
<p>Color support<br/>
Medium quality<br/>
Medium size</p>
<p><a href="/wml/view-image.wml?mid=${encodeURIComponent(messageId)}&amp;jid=${encodeURIComponent(jid)}&amp;format=jpg" accesskey="2">[2] Select JPEG</a></p>

<p><b>3. PNG (Color)</b></p>
<p>High quality color<br/>
Best quality<br/>
Larger size</p>
<p><a href="/wml/view-image.wml?mid=${encodeURIComponent(messageId)}&amp;jid=${encodeURIComponent(jid)}&amp;format=png" accesskey="3">[3] Select PNG</a></p>

<p><a href="/wml/media-info.wml?mid=${encodeURIComponent(messageId)}&amp;jid=${encodeURIComponent(jid)}" accesskey="0">[0] Back</a></p>

<do type="accept" label="${t('common.back')}">
  <go href="/wml/media-info.wml?mid=${encodeURIComponent(messageId)}&amp;jid=${encodeURIComponent(jid)}"/>
</do>`;

    const wmlOutput = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
<head><meta http-equiv="Cache-Control" content="no-cache"/></head>
<card id="format" title="Format">
${body}
</card>
</wml>`;

    sendRawWmlAware(res, wmlOutput);
  } catch (error) {
    logger.error("Image format selection error:", error);
    res.status(500).send("Error loading format selection");
  }
});

// Image viewer with format selection
app.get("/wml/view-image.wml", async (req, res) => {
  try {
    const messageId = req.query.mid || "";
    const jid = req.query.jid || "";
    const format = req.query.format || "wbmp"; // wbmp, jpg, png

    // O(1) lookup via messageStore instead of O(n) .find()
    const targetMessage = messageStore.get(messageId) || null;

    if (!targetMessage || !targetMessage.message?.imageMessage) {
      return sendWml(
        res,
        resultCard("Error", ["Image message not found"], "/wml/chats.wml")
      );
    }

    const contact = contactStore.get(jid);
    const chatName = contact?.name || contact?.notify || jidFriendly(jid);
    const img = targetMessage.message.imageMessage;
    const caption = img.caption || "";

    const esc = (text) =>
      (text || "")
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;");

    // WAP only supports WBMP inline - always display WBMP
    const body = `<p><b>Image Viewer</b></p>
<p>From: ${esc(chatName)}</p>
${caption ? `<p>Caption: ${esc(caption)}</p>` : ''}

<p align="center">
  <img src="/wml/media/${encodeURIComponent(messageId)}.wbmp?wbmp=1" alt="Image"/>
</p>

<p><b>Download Other Formats:</b></p>
<p>
  <a href="/wml/media/${encodeURIComponent(messageId)}.jpg" accesskey="7">[7] Download JPG</a><br/>
  <a href="/wml/media/${encodeURIComponent(messageId)}.png" accesskey="8">[8] Download PNG</a>
</p>

<p>
  <a href="/wml/media-info.wml?mid=${encodeURIComponent(messageId)}&amp;jid=${encodeURIComponent(jid)}" accesskey="0">[0] Back</a>
</p>

<do type="accept" label="${t('common.back')}">
  <go href="/wml/media-info.wml?mid=${encodeURIComponent(messageId)}&amp;jid=${encodeURIComponent(jid)}"/>
</do>`;

    const wmlOutput = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
<head><meta http-equiv="Cache-Control" content="no-cache"/></head>
<card id="image" title="Image">
${body}
</card>
</wml>`;

    sendRawWmlAware(res, wmlOutput);
  } catch (error) {
    logger.error("Image viewer error:", error);
    res.status(500).send("Error loading image");
  }
});

// Nuova route per visualizzare WBMP in una pagina WAP dedicata
app.get("/wml/view-wbmp.wml", async (req, res) => {
  try {
    const messageId = req.query.mid || "";
    const jid = req.query.jid || "";

    // O(1) lookup via messageStore instead of O(n) .find()
    const targetMessage = messageStore.get(messageId) || null;

    const contact = contactStore.get(jid);
    const chatName = contact?.name || contact?.notify || jidFriendly(jid);

    // Simple escaping
    const esc = (text) =>
      (text || "")
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;");

    let body = "";
    let title = "WBMP Image";

    if (targetMessage) {
      const isImage = targetMessage.message?.imageMessage;
      const isSticker = targetMessage.message?.stickerMessage;

      if (isImage || isSticker) {
        const mediaObj = isImage
          ? targetMessage.message.imageMessage
          : targetMessage.message.stickerMessage;
        const size = Math.round((mediaObj.fileLength || 0) / 1024);
        const caption = mediaObj.caption
          ? `<p><b>Caption:</b> ${esc(mediaObj.caption)}</p>`
          : "";

        title = isImage ? "Image (WBMP)" : "Sticker (WBMP)";

        body = `<p><b>${isImage ? "Image" : "Sticker"}</b></p>
<p>From: ${esc(chatName)}</p>
<p>Size: ${size}KB</p>
${caption}
<p>
<img src="/wml/media/${encodeURIComponent(messageId)}.wbmp" alt="WBMP Image"/>
</p>
<p>
<a href="/wml/media-info.wml?mid=${encodeURIComponent(
          messageId
        )}&amp;jid=${encodeURIComponent(
          jid
        )}" accesskey="0">[0] Back to Media Info</a>
</p>
<p>
<a href="/wml/chat.wml?jid=${encodeURIComponent(
          jid
        )}" accesskey="1">[1] Back to Chat</a> |
<a href="/wml/chats.wml" accesskey="9">[9] All Chats</a>
</p>`;
      } else {
        body = `<p><b>Not an Image</b></p>
<p>This message does not contain an image or sticker</p>
<p>
<a href="/wml/media-info.wml?mid=${encodeURIComponent(
          messageId
        )}&amp;jid=${encodeURIComponent(
          jid
        )}" accesskey="0">[0] Back to Media Info</a>
</p>`;
      }
    } else {
      body = `<p><b>Media Not Found</b></p>
<p>Message may have been deleted</p>
<p>
<a href="/wml/chats.wml" accesskey="9">[9] All Chats</a>
</p>`;
    }

    const wmlOutput = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
<head><meta http-equiv="Cache-Control" content="no-cache, no-store"/></head>
<card id="wbmp" title="${title}">
${body}
<do type="accept" label="${t('common.back')}">
<go href="/wml/media-info.wml?mid=${encodeURIComponent(
      messageId
    )}&amp;jid=${encodeURIComponent(jid)}"/>
</do>
<do type="options" label="${t('home.chats')}">
<go href="/wml/chat.wml?jid=${encodeURIComponent(jid)}"/>
</do>
</card>
</wml>`;

    sendRawWmlAware(res, wmlOutput);
  } catch (error) {
    logger.error("WBMP view error:", error);
    res.status(500).send("Error loading WBMP view");
  }
});

/*
app.get('/wml/chat.wml', async (req, res) => {
  const userAgent = req.headers['user-agent'] || ''
  const isOldNokia = /Nokia|Series40|MAUI|UP\.Browser/i.test(userAgent)
  
  const raw = req.query.jid || ''
  const jid = formatJid(raw)
  const offset = Math.max(0, parseInt(req.query.offset || '0'))
  const search = (req.query.search || '').trim().toLowerCase()
  
  // Very small limits for Nokia 7210
  const limit = 3
  
  // Chat history is loaded from persistent storage on startup
  // No need to fetch from WhatsApp servers every time
  
  // Messages stored oldest→newest. For "most recent first" without O(M) copy+reverse:
  const rawMessages = chatStore.get(jid) || [];
  let allMessages, total, items;
  if (search) {
    // Search needs full scan — filter using cached lowercase text
    const searchL = search.toLowerCase();
    allMessages = [];
    for (let i = rawMessages.length - 1; i >= 0; i--) {
      const txt = getMessageSearchText(rawMessages[i]);
      if (txt.includes(searchL)) allMessages.push(rawMessages[i]);
    }
    total = allMessages.length;
    items = allMessages.slice(offset, offset + limit);
  } else {
    // No search: compute reverse window directly — O(limit) instead of O(M)
    total = rawMessages.length;
    const revStart = total - 1 - offset;
    const revEnd = Math.max(-1, revStart - limit);
    items = [];
    for (let i = revStart; i > revEnd && i >= 0; i--) {
      items.push(rawMessages[i]);
    }
  }
  
  const contact = contactStore.get(jid)
  const chatName = contact?.name || contact?.notify || contact?.verifiedName || jidFriendly(jid)
  const number = jidFriendly(jid)
  const isGroup = jid.endsWith('@g.us')
  
  // Simple escaping for Nokia 7210
  const esc = text => (text || '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
  
  // Simple truncate
  const truncate = (text, maxLength) => {
    if (!text) return ''
    if (text.length <= maxLength) return text
    return text.substring(0, maxLength - 3) + '...'
  }
  
  // Simple timestamp for Nokia
  const formatTime = (timestamp) => {
    const date = new Date(Number(timestamp) * 1000)
    if (isNaN(date.getTime())) return ''

    const day = date.getDate().toString().padStart(2, '0')
    const month = (date.getMonth() + 1).toString().padStart(2, '0')
    const year = date.getFullYear()
    const hours = date.getHours().toString().padStart(2, '0')
    const mins = date.getMinutes().toString().padStart(2, '0')
    const secs = date.getSeconds().toString().padStart(2, '0')

    return `${day}/${month}/${year} ${hours}:${mins}:${secs}`
  }
  
  let messageList = ''
  
  if (items.length === 0) {
    messageList = '<p>No messages</p>'
  } else {
    messageList = items.map((m, idx) => {
      const who = m.key.fromMe ? 'Me' : (chatName.length > 10 ? chatName.substring(0, 10) : chatName)
      const time = formatTime(m.messageTimestamp)
      const msgNumber = idx + 1
      const mid = m.key.id
      
      // Handle different message types for Nokia
      let text = ''
      let mediaLink = ''
      
      if (m.message) {
        if (m.message.imageMessage) {
          const img = m.message.imageMessage
          const size = Math.round((img.fileLength || 0) / 1024)
          text = `[IMG ${size}KB]`
          if (img.caption) text += ` ${truncate(img.caption, 30)}`
          mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}">[View IMG]</a>`
          
        } else if (m.message.videoMessage) {
          const vid = m.message.videoMessage
          const size = Math.round((vid.fileLength || 0) / 1024)
          text = `[VID ${size}KB]`
          if (vid.caption) text += ` ${truncate(vid.caption, 30)}`
          mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}">[View VID]</a>`
          
        } else if (m.message.audioMessage) {
          const aud = m.message.audioMessage
          const size = Math.round((aud.fileLength || 0) / 1024)
          const duration = aud.seconds || 0
          text = `[AUD ${size}KB ${duration}s]`
          // Show transcription preview if available
          if (m.transcription && m.transcription !== '[Trascrizione fallita]' && m.transcription !== '[Audio troppo lungo per la trascrizione]') {
            text += `<br/><small>${truncate(m.transcription, 60)}</small>`
          }
          mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}">[View AUD]</a>` +
            ` <a href="/wml/media/${encodeURIComponent(mid)}.mp3">[MP3]</a>` +
            ` <a href="/wml/media/${encodeURIComponent(mid)}.amr">[AMR]</a>`
          
        } else if (m.message.documentMessage) {
          const doc = m.message.documentMessage
          const size = Math.round((doc.fileLength || 0) / 1024)
          const filename = doc.fileName || 'file'
          text = `[DOC ${size}KB] ${truncate(filename, 20)}`
          mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}">[View DOC]</a>`
          
        } else if (m.message.stickerMessage) {
          text = '[STICKER]'
          mediaLink = `<br/><a href="/wml/media-info.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}">[View STK]</a>`
          
        } else {
          text = truncate(messageText(m) || '', 50)
        }
      } else {
        text = truncate(messageText(m) || '', 50)
      }
      
      return `<p>${msgNumber}. ${esc(who)} (${time})<br/>${esc(text)}${mediaLink}</p>`
    }).join('')
  }
  
  // Simple navigation for Nokia
  const olderOffset = offset + limit
  const olderLink = olderOffset < total ? 
    `<p><a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}&amp;offset=${olderOffset}&amp;search=${encodeURIComponent(search)}" accesskey="2">2-Older</a></p>` : ''
  
  const newerOffset = Math.max(0, offset - limit)
  const newerLink = offset > 0 ? 
    `<p><a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}&amp;offset=${newerOffset}&amp;search=${encodeURIComponent(search)}" accesskey="3">3-Newer</a></p>` : ''
  
  // Simple search for Nokia
  const searchBox = search ? 
    `<p>Search: ${esc(search)}</p><p><a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}">Clear</a></p>` : 
    `<p><a href="/wml/chat.wml?jid=${encodeURIComponent(jid)}&amp;search=prompt">Search</a></p>`
  
  const body = `<p>${esc(chatName.length > 15 ? chatName.substring(0, 15) : chatName)}</p>
<p>Msgs ${offset + 1}-${Math.min(offset + limit, total)}/${total}</p>
${searchBox}
${messageList}
${newerLink}
${olderLink}
<p><a href="/wml/send.text.wml?to=${encodeURIComponent(jid)}" accesskey="1">1-Send</a></p>
<p><a href="/wml/chats.wml" accesskey="0">0-Back</a></p>`
  
  // Nokia 7210 compatible WML 1.1
  const wmlOutput = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
<head><meta http-equiv="Cache-Control" content="no-cache, no-store"/></head>
<card id="chat" title="Chat">
${body}
</card>
</wml>`
  
  // Nokia 7210 headers
  res.setHeader('Content-Type', 'text/vnd.wap.wml; charset=iso-8859-1')
  res.setHeader('Cache-Control', 'no-cache')
  res.setHeader('Pragma', 'no-cache')
  
  const encodedBuffer = iconv.encode(wmlOutput, 'iso-8859-1')
  res.send(encodedBuffer)
})*/
// Enhanced Message Actions page
app.get("/wml/msg.wml", (req, res) => {
  const mid = String(req.query.mid || "");
  const jid = formatJid(req.query.jid || "");

  // O(1) lookup via messageStore instead of O(n) .find()
  const msg = messageStore.get(mid) || null;

  if (!msg) {
    sendWml(
      res,
      resultCard(
        "Message",
        ["Message not found"],
        `/wml/chat.wml?jid=${encodeURIComponent(jid)}&limit=3`
      )
    );
    return;
  }

  const text = truncate(messageText(msg), 150);
  const tsDate = new Date(Number(msg.messageTimestamp) * 1000);
  const ts = tsDate.toLocaleDateString('en-GB', { day: '2-digit', month: '2-digit', year: 'numeric' }) + ' ' + tsDate.toLocaleTimeString('en-GB', { hour: '2-digit', minute: '2-digit', second: '2-digit' });

  // Enhanced media detection
  let mediaInfo = "";
  let mediaActions = "";
  let hasMedia = false;
  let transcriptionInfo = "";
  let transcriptionActions = "";

  if (msg.message) {
    if (msg.message.imageMessage) {
      const img = msg.message.imageMessage;
      const size = Math.round((img.fileLength || 0) / 1024);
      mediaInfo = `<p><small>Type: Image (${size}KB)</small></p>`;
      mediaActions = `<a href="/wml/media-info.wml?mid=${encodeURIComponent(
        mid
      )}&amp;jid=${encodeURIComponent(
        jid
      )}" accesskey="4">[4] View Image</a><br/>
      <a href="/wml/media/${encodeURIComponent(
        mid
      )}.jpg" accesskey="5">[5] Download JPG</a><br/>`;
      hasMedia = true;
    } else if (msg.message.videoMessage) {
      const vid = msg.message.videoMessage;
      const size = Math.round((vid.fileLength || 0) / 1024);
      const duration = vid.seconds || 0;
      mediaInfo = `<p><small>Type: Video (${size}KB, ${duration}s)</small></p>`;
      mediaActions = `<a href="/wml/media-info.wml?mid=${encodeURIComponent(
        mid
      )}&amp;jid=${encodeURIComponent(
        jid
      )}" accesskey="4">[4] View Video</a><br/>
      <a href="/wml/media/${encodeURIComponent(
        mid
      )}.mp4" accesskey="5">[5] Download MP4</a><br/>`;
      hasMedia = true;
    } else if (msg.message.audioMessage) {
      const aud = msg.message.audioMessage;
      const size = Math.round((aud.fileLength || 0) / 1024);
      const duration = aud.seconds || 0;

      mediaInfo = `<p><small>Type: Audio (${size}KB, ${duration}s)</small></p>
      <p><b>Download Audio:</b></p>
      <p>
        <a href="/wml/media/${encodeURIComponent(mid)}.mp3" accesskey="4">[4] MP3</a> |
        <a href="/wml/media/${encodeURIComponent(mid)}.amr">[AMR]</a> |
        <a href="/wml/media/${encodeURIComponent(mid)}.wav">[WAV]</a> |
        <a href="/wml/media/${encodeURIComponent(mid)}.ogg">[OGG]</a>
      </p>
      <p><b>Stream:</b></p>
      <p>
        <a href="/wml/stream/audio/${encodeURIComponent(mid)}.ram?format=amr" accesskey="5">[5] RealPlayer AMR</a> |
        <a href="/wml/stream/audio/${encodeURIComponent(mid)}.ram?format=mp3">[MP3]</a>
      </p>`;

      hasMedia = true;

      // Gestione trascrizione
      if (msg.transcription) {
        if (msg.transcription === "[Trascrizione fallita]") {
          transcriptionInfo = `<p><small>${t('audio.transcription')} ${t('audio.failed_short')}</small></p>`;
        } else if (
          msg.transcription === "[Audio troppo lungo per la trascrizione]"
        ) {
          transcriptionInfo = `<p><small>${t('audio.transcription')} ${t('audio.too_long_short')}</small></p>`;
        } else {
          transcriptionInfo = `<p><small>${t('audio.transcription')} ${truncate(msg.transcription, 80)}</small></p>`;
          transcriptionActions = `<a href="/wml/audio-transcription.wml?mid=${encodeURIComponent(
            mid
          )}&amp;jid=${encodeURIComponent(
            jid
          )}" accesskey="6">[6] Full Transcription</a><br/>`;
        }
      } else {
        transcriptionInfo = `<p><small>${t('audio.transcription')} ${t('audio.in_progress_short')}</small></p>`;
      }
    } else if (msg.message.documentMessage) {
      const doc = msg.message.documentMessage;
      const size = Math.round((doc.fileLength || 0) / 1024);
      const filename = doc.fileName || "document";
      mediaInfo = `<p><small>Type: Document (${size}KB)</small></p>
      <p><small>File: ${esc(filename)}</small></p>`;
      const ext = filename.split(".").pop() || "bin";
      mediaActions = `<a href="/wml/media-info.wml?mid=${encodeURIComponent(
        mid
      )}&amp;jid=${encodeURIComponent(
        jid
      )}" accesskey="4">[4] View Document</a><br/>
      <a href="/wml/media/${encodeURIComponent(
        mid
      )}.${ext}" accesskey="5">[5] Download File</a><br/>`;
      hasMedia = true;
    } else if (msg.message.stickerMessage) {
      const sticker = msg.message.stickerMessage;
      const content = extractMessageContent(msg.message);
      const inlineText = extractInlineTextFromContent(content);
      const stickerHuman = stickerTextWithOptionalText(sticker, inlineText, false);
      mediaInfo = `<p><small>Type: ${esc(stickerHuman)}</small></p>
      <p><img src="/wml/media/${encodeURIComponent(mid)}.wbmp" alt="Sticker"/></p>`;
      mediaActions = `<a href="/wml/media-info.wml?mid=${encodeURIComponent(
        mid
      )}&amp;jid=${encodeURIComponent(
        jid
      )}" accesskey="4">[4] View Sticker</a><br/>
      <a href="/wml/media/${encodeURIComponent(
        mid
      )}.wbmp" accesskey="5">[5] WBMP (Nokia)</a><br/>
      <a href="/wml/media/${encodeURIComponent(
        mid
      )}.jpg" accesskey="6">[6] JPG</a><br/>
      ${
        sticker.isAnimated
          ? `<a href="/wml/media/${encodeURIComponent(mid)}.gif" accesskey="9">[9] GIF</a><br/>`
          : ""
      }`;
      hasMedia = true;
    }
  }

  const body = `
    <p><b>${t('msg.title')}</b></p>
    <p>${esc(text)}</p>
    <p><small>${t('msg.time')} ${ts}</small></p>
    <p><small>${t('msg.from')} ${msg.key.fromMe ? t('chat.me') : "Them"}</small></p>
    ${mediaInfo}
    ${transcriptionInfo}

    <p><b>${t('msg.actions')}</b></p>
    <p>
      <a href="/wml/msg.reply.wml?mid=${encodeURIComponent(
        mid
      )}&amp;jid=${encodeURIComponent(jid)}" accesskey="1">${t('msg.reply')}</a><br/>
      <a href="/wml/msg.react.wml?mid=${encodeURIComponent(
        mid
      )}&amp;jid=${encodeURIComponent(jid)}" accesskey="2">${t('msg.react')}</a><br/>
      <a href="/wml/msg.forward.wml?mid=${encodeURIComponent(
        mid
      )}" accesskey="3">${t('msg.forward')}</a><br/>
      ${mediaActions}
      ${transcriptionActions}
      <a href="/wml/msg.delete.wml?mid=${encodeURIComponent(
        mid
      )}&amp;jid=${encodeURIComponent(jid)}" accesskey="7">${t('msg.delete')}</a><br/>
      <a href="/wml/msg.read.wml?mid=${encodeURIComponent(
        mid
      )}&amp;jid=${encodeURIComponent(
    jid
  )}" accesskey="8">${t('msg.mark_read')}</a><br/>
    </p>

    <p><a href="/wml/chat.wml?jid=${encodeURIComponent(
      jid
    )}&amp;limit=3" accesskey="0">${t('msg.back')}</a></p>

    <do type="accept" label="${t('msg.reply')}">
      <go href="/wml/msg.reply.wml?mid=${encodeURIComponent(
        mid
      )}&amp;jid=${encodeURIComponent(jid)}"/>
    </do>
    ${
      hasMedia || transcriptionActions
        ? `<do type="options" label="${t('common.media')}">
      <go href="/wml/media-info.wml?mid=${encodeURIComponent(
        mid
      )}&amp;jid=${encodeURIComponent(jid)}"/>
    </do>`
        : ""
    }
  `;

  sendWml(res, card("msg", t('msg.title'), body));
});

// =================== MESSAGE ACTION ROUTES ===================

app.get("/wml/msg.reply.wml", (req, res) => {
  const mid = req.query.mid || "";
  const jid = req.query.jid || "";
  const msg = messageStore.get(mid);
  if (!msg) {
    return sendWml(res, resultCard("Error", ["Message not found"], `/wml/chat.wml?jid=${encodeURIComponent(jid)}&limit=3`));
  }
  const preview = truncate(messageText(msg) || "[media]", 40);
  const body = `
    <p><b>${t('msg.reply')}</b></p>
    <p><small>Re: ${esc(preview)}</small></p>
    <p>Your message:</p>
    <input name="message" title="Message" size="30" maxlength="1000"/>
    <p>
      <anchor title="Send">Send
        <go method="post" href="/wml/msg.reply">
          <postfield name="mid" value="${esc(mid)}"/>
          <postfield name="jid" value="${esc(jid)}"/>
          <postfield name="message" value="$(message)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.send')}">
      <go method="post" href="/wml/msg.reply">
        <postfield name="mid" value="${esc(mid)}"/>
        <postfield name="jid" value="${esc(jid)}"/>
        <postfield name="message" value="$(message)"/>
      </go>
    </do>
    <p><a href="/wml/msg.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}" accesskey="0">[0] Cancel</a></p>
  `;
  sendWml(res, card("msg-reply", t('msg.reply'), body));
});

app.post("/wml/msg.reply", async (req, res) => {
  const { mid, jid, message } = req.body;
  try {
    if (!sock) throw new Error("Not connected");
    const quotedMessage = messageStore.get(mid);
    if (!quotedMessage) throw new Error("Original message not found");
    await sock.sendMessage(formatJid(jid), { text: message }, { quoted: quotedMessage });
    sendWml(res, resultCard("Sent", [`Reply sent to ${jidFriendly(jid)}`], `/wml/chat.wml?jid=${encodeURIComponent(jid)}&limit=3`));
  } catch (e) {
    sendWml(res, resultCard("Error", [e.message || "Send failed"], `/wml/msg.reply.wml?mid=${encodeURIComponent(mid)}&jid=${encodeURIComponent(jid)}`));
  }
});

app.get("/wml/msg.react.wml", (req, res) => {
  const mid = req.query.mid || "";
  const jid = req.query.jid || "";
  const msg = messageStore.get(mid);
  if (!msg) {
    return sendWml(res, resultCard("Error", ["Message not found"], `/wml/chat.wml?jid=${encodeURIComponent(jid)}&limit=3`));
  }
  const preview = truncate(messageText(msg) || "[media]", 40);
  const body = `
    <p><b>${t('msg.react')}</b></p>
    <p><small>${esc(preview)}</small></p>
    <p>Choose reaction:</p>
    <select name="emoji" title="Reaction">
      <option value="&#128077;">Thumbs Up</option>
      <option value="&#10084;">Heart</option>
      <option value="&#128518;">Laugh</option>
      <option value="&#128562;">Surprised</option>
      <option value="&#128546;">Sad</option>
      <option value="&#128079;">Clap</option>
      <option value="">Remove</option>
    </select>
    <p>
      <anchor title="React">React
        <go method="post" href="/wml/msg.react">
          <postfield name="mid" value="${esc(mid)}"/>
          <postfield name="jid" value="${esc(jid)}"/>
          <postfield name="emoji" value="$(emoji)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.react')}">
      <go method="post" href="/wml/msg.react">
        <postfield name="mid" value="${esc(mid)}"/>
        <postfield name="jid" value="${esc(jid)}"/>
        <postfield name="emoji" value="$(emoji)"/>
      </go>
    </do>
    <p><a href="/wml/msg.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}" accesskey="0">[0] Cancel</a></p>
  `;
  sendWml(res, card("msg-react", t('msg.react'), body));
});

app.post("/wml/msg.react", async (req, res) => {
  const { mid, jid, emoji } = req.body;
  try {
    if (!sock) throw new Error("Not connected");
    const targetMessage = messageStore.get(mid);
    if (!targetMessage) throw new Error("Message not found");
    await sock.sendMessage(formatJid(jid), { react: { text: emoji || "", key: targetMessage.key } });
    const label = emoji ? "Reaction sent" : "Reaction removed";
    sendWml(res, resultCard("Done", [label], `/wml/chat.wml?jid=${encodeURIComponent(jid)}&limit=3`));
  } catch (e) {
    sendWml(res, resultCard("Error", [e.message || "React failed"], `/wml/msg.react.wml?mid=${encodeURIComponent(mid)}&jid=${encodeURIComponent(jid)}`));
  }
});

app.get("/wml/msg.forward.wml", (req, res) => {
  const mid = req.query.mid || "";
  const search = (req.query.search || "").toLowerCase();
  const page = parseInt(req.query.page || "1", 10);
  const pageSize = 5;
  const msg = messageStore.get(mid);
  if (!msg) {
    return sendWml(res, resultCard("Error", ["Message not found"], "/wml/home.wml"));
  }
  const preview = truncate(messageText(msg) || "[media]", 30);
  const allContacts = [];
  for (const [cjid, contact] of contactStore) {
    if (!cjid.endsWith("@s.whatsapp.net") && !cjid.endsWith("@g.us")) continue;
    const name = contact?.name || contact?.notify || jidFriendly(cjid);
    if (!name) continue;
    if (search && !name.toLowerCase().includes(search)) continue;
    allContacts.push({ jid: cjid, name });
  }
  allContacts.sort((a, b) => a.name.localeCompare(b.name));
  const totalPages = Math.max(1, Math.ceil(allContacts.length / pageSize));
  const pageContacts = allContacts.slice((page - 1) * pageSize, page * pageSize);
  const contactList = pageContacts.map((c) =>
    `<p><anchor>${esc(c.name)}<go method="post" href="/wml/msg.forward"><postfield name="mid" value="${esc(mid)}"/><postfield name="to" value="${esc(c.jid)}"/></go></anchor></p>`
  ).join("");
  const prevLink = page > 1 ? `<a href="/wml/msg.forward.wml?mid=${encodeURIComponent(mid)}&amp;page=${page - 1}" accesskey="7">[7] Prev</a> ` : "";
  const nextLink = page < totalPages ? `<a href="/wml/msg.forward.wml?mid=${encodeURIComponent(mid)}&amp;page=${page + 1}" accesskey="8">[8] Next</a>` : "";
  const body = `
    <p><b>${t('msg.forward')}</b></p>
    <p><small>Fwd: ${esc(preview)}</small></p>
    <p>Choose recipient:</p>
    ${contactList || "<p><em>No contacts found</em></p>"}
    ${(prevLink || nextLink) ? `<p>${prevLink}${nextLink}</p>` : ""}
    <p><a href="/wml/msg.wml?mid=${encodeURIComponent(mid)}" accesskey="0">[0] Cancel</a></p>
  `;
  sendWml(res, card("msg-forward", t('msg.forward'), body));
});

app.post("/wml/msg.forward", async (req, res) => {
  const { mid, to } = req.body;
  try {
    if (!sock) throw new Error("Not connected");
    const targetMessage = messageStore.get(mid);
    if (!targetMessage) throw new Error("Message not found");
    if (!targetMessage.message) throw new Error("Cannot forward this message type");
    await sock.relayMessage(formatJid(to), targetMessage.message, {});
    sendWml(res, resultCard("Forwarded", [`Message forwarded to ${jidFriendly(to)}`], `/wml/chat.wml?jid=${encodeURIComponent(to)}&limit=3`));
  } catch (e) {
    sendWml(res, resultCard("Error", [e.message || "Forward failed"], `/wml/msg.forward.wml?mid=${encodeURIComponent(mid)}`));
  }
});

app.get("/wml/msg.delete.wml", (req, res) => {
  const mid = req.query.mid || "";
  const jid = req.query.jid || "";
  const msg = messageStore.get(mid);
  if (!msg) {
    return sendWml(res, resultCard("Error", ["Message not found"], `/wml/chat.wml?jid=${encodeURIComponent(jid)}&limit=3`));
  }
  const preview = truncate(messageText(msg) || "[media]", 40);
  const body = `
    <p><b>${t('msg.delete')}</b></p>
    <p>Delete this message?</p>
    <p><small>${esc(preview)}</small></p>
    <p>
      <anchor title="Delete">Yes, Delete
        <go method="post" href="/wml/msg.delete">
          <postfield name="mid" value="${esc(mid)}"/>
          <postfield name="jid" value="${esc(jid)}"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.delete')}">
      <go method="post" href="/wml/msg.delete">
        <postfield name="mid" value="${esc(mid)}"/>
        <postfield name="jid" value="${esc(jid)}"/>
      </go>
    </do>
    <p><a href="/wml/msg.wml?mid=${encodeURIComponent(mid)}&amp;jid=${encodeURIComponent(jid)}" accesskey="0">[0] Cancel</a></p>
  `;
  sendWml(res, card("msg-delete", t('msg.delete'), body));
});

app.post("/wml/msg.delete", async (req, res) => {
  const { mid, jid } = req.body;
  try {
    if (!sock) throw new Error("Not connected");
    const targetMessage = messageStore.get(mid);
    if (!targetMessage) throw new Error("Message not found");
    await sock.sendMessage(formatJid(jid), { delete: targetMessage.key });
    // Remove from local stores
    messageStore.delete(mid);
    const chatId = formatJid(jid);
    const chatMessages = chatStore.get(chatId);
    if (chatMessages) {
      const idx = chatMessages.findIndex(m => m.key?.id === mid);
      if (idx !== -1) chatMessages.splice(idx, 1);
    }
    chatMessageIdSets.get(chatId)?.delete(mid);
    sendWml(res, resultCard("Deleted", ["Message deleted"], `/wml/chat.wml?jid=${encodeURIComponent(jid)}&limit=3`));
  } catch (e) {
    sendWml(res, resultCard("Error", [e.message || "Delete failed"], `/wml/msg.delete.wml?mid=${encodeURIComponent(mid)}&jid=${encodeURIComponent(jid)}`));
  }
});

// Mark as read — only resets local unread counter (no WhatsApp API call to prevent bans)
app.get("/wml/msg.read.wml", (req, res) => {
  const jid = req.query.jid || "";
  const chatId = formatJid(jid);
  perChatUnreadCount.set(chatId, 0);
  cachedUnreadCount = -1;
  perfCache.invalidateChats();
  sendWml(res, resultCard("Done", ["Chat marked as read"], `/wml/chat.wml?jid=${encodeURIComponent(jid)}&limit=3`));
});

app.get("/wml/send-menu.wml", (req, res) => {
  const to = esc(req.query.to || "");
  const search = (req.query.search || "").toLowerCase();
  const page = parseInt(req.query.page || "1", 10);
  const pageSize = 3;
  const contact = to
    ? contactStore.get(formatJid(to))
    : null;
  const contactName = contact?.name || contact?.notify || jidFriendly(to) || "";

  // Filter contacts inline from iterator — no Array.from() copy + pre-lowercase
  const searchL = search ? search.toLowerCase() : '';
  const filteredContacts = [];
  for (const c of contactStore.values()) {
    if (!searchL || (c.name || c.notify || '').toLowerCase().includes(searchL)) {
      filteredContacts.push(c);
    }
  }

  const totalPages = Math.ceil(filteredContacts.length / pageSize);
  const currentPage = Math.min(Math.max(page, 1), totalPages || 1);
  const start = (currentPage - 1) * pageSize;
  const pageContacts = filteredContacts.slice(start, start + pageSize);

  // Debug: verifica i contatti
  console.log("Total contacts:", contactStore.size);
  console.log("Filtered contacts:", filteredContacts.length);
  console.log("Page contacts:", pageContacts.length);
  console.log("Sample contact:", pageContacts[0]);

  const selectOptions = pageContacts
    .map((c) => {
      const displayName = c.name || c.notify || jidFriendly(c.jid) || c.jid;
      const jidValue = c.jid || c.id || "";
      console.log("Contact option:", displayName, "->", jidValue);
      return `<option value="${esc(jidValue)}"${
        jidValue === to ? ' selected="selected"' : ""
      }>${esc(displayName)}</option>`;
    })
    .join("");

  // Costruisci paginazione "max 5 numeri" con First / Last / Back / Next
  let pagination = "";
  if (totalPages > 1) {
    pagination += "<p>";
    // First
    if (currentPage > 1) {
      pagination += `<a href="/wml/send-menu.wml?to=${encodeURIComponent(
        to
      )}&amp;search=${encodeURIComponent(search)}&amp;page=1">First</a> `;
      pagination += `<a href="/wml/send-menu.wml?to=${encodeURIComponent(
        to
      )}&amp;search=${encodeURIComponent(search)}&amp;page=${
        currentPage - 1
      }">Back</a> `;
    }
    // Calcola range di 5 numeri centrati sulla pagina corrente
    let startPage = Math.max(1, currentPage - 2);
    let endPage = Math.min(totalPages, startPage + 4);
    if (endPage - startPage < 4) startPage = Math.max(1, endPage - 4);
    for (let i = startPage; i <= endPage; i++) {
      if (i === currentPage) pagination += `<b>${i}</b> `;
      else
        pagination += `<a href="/wml/send-menu.wml?to=${encodeURIComponent(
          to
        )}&amp;search=${encodeURIComponent(search)}&amp;page=${i}">${i}</a> `;
    }
    // Next / Last
    if (currentPage < totalPages) {
      pagination += `<a href="/wml/send-menu.wml?to=${encodeURIComponent(
        to
      )}&amp;search=${encodeURIComponent(search)}&amp;page=${
        currentPage + 1
      }">Next</a> `;
      pagination += `<a href="/wml/send-menu.wml?to=${encodeURIComponent(
        to
      )}&amp;search=${encodeURIComponent(
        search
      )}&amp;page=${totalPages}">Last</a>`;
    }
    pagination += "</p>";
  }

  const body = `
    <p><b>${t('send_menu.title')}</b></p>
    ${to ? `<p>${t('send_menu.to')} <b>${esc(contactName)}</b></p>` : ""}
    <p>${t('send_menu.search_contacts')}</p>
    <p>
      <input name="search" value="${esc(
        req.query.search || ""
      )}" size="15" iname="search"/>
    </p>
    <p>
      <anchor title="Filter">Filter
        <go href="/wml/send-menu.wml">
          <postfield name="to" value="${esc(to)}"/>
          <postfield name="search" value="$(search)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.filter')}">
      <go href="/wml/send-menu.wml">
        <postfield name="to" value="${esc(to)}"/>
        <postfield name="search" value="$(search)"/>
      </go>
    </do>

    <p>${t('send_menu.select_contact')} (${t('common.page')} ${currentPage} ${t('common.of')} ${totalPages || 1}):</p>
    <select name="target" title="Contact">
      <option value="">${t('send_menu.enter_manually')}</option>
      ${selectOptions}
    </select>
    <p>
      <anchor title="${t('send_menu.set_contact')}">${t('send_menu.set_contact')}
        <go href="/wml/send-menu.wml">
          <postfield name="to" value="$target"/>
          <postfield name="search" value="${esc(search)}"/>
          <postfield name="page" value="${currentPage}"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('send_menu.set_contact')}">
      <go href="/wml/send-menu.wml">
        <postfield name="to" value="$target"/>
        <postfield name="search" value="${esc(search)}"/>
        <postfield name="page" value="${currentPage}"/>
      </go>
    </do>
    ${pagination}

    ${
      to
        ? `<p><a href="/wml/send-menu.wml?search=${encodeURIComponent(
            search
          )}&amp;page=${currentPage}">${t('send_menu.clear')}</a></p>`
        : ""
    }
    <p>${t('send_menu.enter_number')}</p>
    <p>
      <input name="target_manual" value="${esc(to)}" size="15" title="Manual"/>
    </p>
    <p>
      <anchor title="${t('send_menu.set_manual')}">${t('send_menu.set_manual')}
        <go href="/wml/send-menu.wml">
          <postfield name="to" value="$target_manual"/>
          <postfield name="search" value="${esc(search)}"/>
          <postfield name="page" value="${currentPage}"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('send_menu.set_manual')}">
      <go href="/wml/send-menu.wml">
        <postfield name="to" value="$target_manual"/>
        <postfield name="search" value="${esc(search)}"/>
        <postfield name="page" value="${currentPage}"/>
      </go>
    </do>
    <p><b>${t('send_menu.message_types')}</b></p>
    <select name="msgtype" title="Type" iname="msgtype" ivalue="/wml/send.text.wml">
      <option value="/wml/send.text.wml">${t('send_menu.text')}</option>
      <option value="/wml/send.tts.wml">${t('send_menu.voice')}</option>
      <option value="/wml/send.image.wml">${t('send_menu.image')}</option>
      <option value="/wml/send.video.wml">${t('send_menu.video')}</option>
      <option value="/wml/send.audio.wml">${t('send_menu.audio')}</option>
      <option value="/wml/send.document.wml">${t('send_menu.document')}</option>
      <option value="/wml/send.sticker.wml">${t('send_menu.sticker')}</option>
      <option value="/wml/send.location.wml">${t('send_menu.location')}</option>
      <option value="/wml/send.contact.wml">${t('send_menu.contact')}</option>
      <option value="/wml/send.poll.wml">${t('send_menu.poll')}</option>
    </select>

    <p>
      <anchor title="${t('send_menu.send')}">${t('send_menu.send')}
        <go href="/wml/send-dispatch.wml" method="post">
          <postfield name="msgtype" value="$(msgtype)"/>
          <postfield name="target" value="$(target)"/>
          <postfield name="target_manual" value="$(target_manual)"/>
        </go>
      </anchor>
    </p>
<do type="accept" label="${t('send_menu.send')}">
  <go href="/wml/send-dispatch.wml" method="post">
    <postfield name="msgtype" value="$(msgtype)"/>
    <postfield name="target" value="$(target)"/>
    <postfield name="target_manual" value="$(target_manual)"/>
  </go>
</do>



    <do type="accept" label="Reset All ">
      <go href="/wml/send-menu.wml" method="post">

      </go>
    </do>


    ${navigationBar()}
    <do type="options" label="${t('contacts.title')}">
      <go href="/wml/contacts.wml"/>
    </do>
  `;

  sendWml(res, card("send-menu", t('send_menu.title'), body));
});

// Quick Send - Streamlined for known contacts (FAST, non-blocking)
// Use this when contact is already known from chat/contact info
app.get("/wml/send-quick.wml", (req, res) => {
  const to = req.query.to || "";

  if (!to) {
    // No contact specified, redirect to full menu
    return authRedirect(res, "/wml/send-menu.wml");
  }

  // Fast lookup - non-blocking
  const jid = formatJid(to);
  const contact = contactStore.get(jid);
  const contactName = contact?.name || contact?.notify || jidFriendly(to);

  // Minimal, fast HTML - optimized for Nokia WAP
  const body = `
    <p><b>Quick Send</b></p>
    <p>To: <b>${esc(contactName)}</b></p>
    <p>Number: ${esc(jidFriendly(to))}</p>

    <p>Select type:</p>
    <select name="msgtype" title="Type">
      <option value="/wml/send.text.wml">Text</option>
      <option value="/wml/send.tts.wml">Voice (TTS)</option>
      <option value="/wml/send.image.wml">Image</option>
      <option value="/wml/send.video.wml">Video</option>
      <option value="/wml/send.audio.wml">Audio</option>
      <option value="/wml/send.document.wml">Document</option>
      <option value="/wml/send.sticker.wml">Sticker</option>
      <option value="/wml/send.location.wml">Location</option>
      <option value="/wml/send.contact.wml">Contact</option>
      <option value="/wml/send.poll.wml">Poll</option>
    </select>

    <p>
      <anchor title="Continue">Continue
        <go href="/wml/send-dispatch.wml" method="get">
          <postfield name="msgtype" value="$(msgtype)"/>
          <postfield name="target" value="${esc(to)}"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.continue')}">
      <go href="/wml/send-dispatch.wml" method="get">
        <postfield name="msgtype" value="$(msgtype)"/>
        <postfield name="target" value="${esc(to)}"/>
      </go>
    </do>

    <p>
      <a href="/wml/send-menu.wml" accesskey="0">[0] Full Menu</a> |
      <a href="/wml/chats.wml" accesskey="9">[9] Chats</a>
    </p>
  `;

  // Fast response - minimal processing
  sendWml(res, card("send-quick", "Quick Send", body));
});

// Route di dispatch per gestire la selezione del destinatario
// Uses simple HTTP redirect for Nokia WAP compatibility
app.post("/wml/send-dispatch.wml", (req, res) => {
  const msgtype = req.body.msgtype || "/wml/send.text.wml";
  const target = req.body.target || "";
  const targetManual = req.body.target_manual || "";

  // Debug: log dei parametri ricevuti
  console.log(
    "Dispatch POST - msgtype:",
    msgtype,
    "target:",
    target,
    "target_manual:",
    targetManual
  );

  // Determina il destinatario: priorità al contatto selezionato, altrimenti manuale
  const finalTarget = target || targetManual;

  if (!finalTarget) {
    // Nessun destinatario specificato, torna al menu con errore
    const body = `
      <p><b>Error</b></p>
      <p>Please select a contact or enter a number manually.</p>
      <p>Debug info: target="${esc(target)}", manual="${esc(targetManual)}"</p>
      <p><a href="/wml/send-menu.wml">Back to Send Menu</a></p>
      ${navigationBar()}
    `;
    return sendWml(res, card("error", "Error", body));
  }

  // Simple HTTP redirect - works on all Nokia WAP devices
  const redirectUrl = `${msgtype}?to=${encodeURIComponent(finalTarget)}`;
  console.log("Redirecting to:", redirectUrl);

  authRedirect(res, redirectUrl);
});

// Versione GET per fallback - Nokia WAP compatible
app.get("/wml/send-dispatch.wml", (req, res) => {
  const msgtype = req.query.msgtype || "/wml/send.text.wml";
  const target = req.query.target || "";
  const targetManual = req.query.target_manual || "";

  const finalTarget = target || targetManual;

  if (!finalTarget) {
    const body = `
      <p><b>Error</b></p>
      <p>Please select a contact or enter a number manually.</p>
      <p><a href="/wml/send-menu.wml">Back to Send Menu</a></p>
      ${navigationBar()}
    `;
    return sendWml(res, card("error", "Error", body));
  }

  const redirectUrl = `${msgtype}?to=${encodeURIComponent(finalTarget)}`;

  authRedirect(res, redirectUrl);
});

// Enhanced Send Text with templates
app.get("/wml/send.text.wml", (req, res) => {
  const to = esc(req.query.to || "");
  const template = req.query.template || "";

  const templates = [
    "Hello! How are you?",
    "Thanks for your message.",
    "I will call you back later.",
    "Please send me the details.",
    "Meeting confirmed for today.",
  ];

  const body = `
    <p><b>${t('send_text.title')}</b></p>
    <p>${t('send_menu.to')} <input name="to" title="${t('send_text.recipient')}" value="${to}" size="15"/></p>

    <p>${t('send_text.message')}</p>
    <input name="message" title="${t('send_text.placeholder')}" value="${esc(
      template
    )}" size="30" maxlength="1000"/>

    ${
      template
        ? ""
        : `
    <p><b>${t('send_text.templates')}</b></p>
    <select name="tmpl" title="${t('send_text.quick_templates')}">
      ${templates
        .map(
          (tmpl, i) =>
            `<option value="${esc(tmpl)}">${i + 1}. ${esc(
              truncate(tmpl, 20)
            )}</option>`
        )
        .join("")}
    </select>
    <do type="options" label="${t('common.use')}">
      <refresh>
        <setvar name="message" value="$(tmpl)"/>
      </refresh>
    </do>
    `
    }

    <p>
      <anchor title="${t('send_text.send')}">${t('send_text.send')}
        <go method="post" href="/wml/send.text">
          <postfield name="to" value="$(to)"/>
          <postfield name="message" value="$(message)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('send_text.send')}">
      <go method="post" href="/wml/send.text">
        <postfield name="to" value="$(to)"/>
        <postfield name="message" value="$(message)"/>
      </go>
    </do>

    <p>
      <a href="/wml/send-menu.wml?to=${encodeURIComponent(
        to
      )}" accesskey="0">${t('send_text.back')}</a>
      <a href="/wml/contacts.wml" accesskey="9">${t('send_text.contacts')}</a>
    </p>
  `;

  sendWml(res, card("send-text", t('send_text.title'), body));
});

// Endpoint per inviare immagini
app.get("/wml/send.image.wml", (req, res) => {
  const to = esc(req.query.to || "");

  const body = `
    <p><b>${t('send_image.title')}</b></p>
    <p>${t('send_menu.to')} <input name="to" title="${t('send_text.recipient')}" value="${to}" size="15"/></p>

    <p>${t('send_image.url')}</p>
    <input name="imageUrl" title="Image URL" value="https://" size="30" maxlength="500"/>

    <p>${t('send_image.caption')}</p>
    <input name="caption" title="${t('send_image.caption_placeholder')}" value="" size="30" maxlength="1000"/>

    <p><small>${t('send_image.formats')}</small></p>

    <p>
      <anchor title="${t('send_image.send')}">${t('send_image.send')}
        <go method="post" href="/wml/send.image">
          <postfield name="to" value="$(to)"/>
          <postfield name="imageUrl" value="$(imageUrl)"/>
          <postfield name="caption" value="$(caption)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('send_image.send')}">
      <go method="post" href="/wml/send.image">
        <postfield name="to" value="$(to)"/>
        <postfield name="imageUrl" value="$(imageUrl)"/>
        <postfield name="caption" value="$(caption)"/>
      </go>
    </do>

    <p>
      <a href="/wml/send-menu.wml?to=${encodeURIComponent(
        to
      )}" accesskey="0">${t('send_text.back')}</a>
      <a href="/wml/contacts.wml" accesskey="9">${t('send_text.contacts')}</a>
    </p>
  `;

  sendWml(res, card("send-image", t('send_image.title'), body));
});

// Endpoint per inviare video
app.get("/wml/send.video.wml", (req, res) => {
  const to = esc(req.query.to || "");

  const body = `
    <p><b>${t('send_video.title')}</b></p>
    <p>${t('send_menu.to')} <input name="to" title="${t('send_text.recipient')}" value="${to}" size="15"/></p>

    <p>${t('send_video.url')}</p>
    <input name="videoUrl" title="Video URL" value="https://" size="30" maxlength="500"/>

    <p>${t('send_video.caption')}</p>
    <input name="caption" title="${t('send_video.caption_placeholder')}" value="" size="30" maxlength="1000"/>

    <p><small>${t('send_video.formats')}</small></p>

    <p>
      <anchor title="${t('send_video.send')}">${t('send_video.send')}
        <go method="post" href="/wml/send.video">
          <postfield name="to" value="$(to)"/>
          <postfield name="videoUrl" value="$(videoUrl)"/>
          <postfield name="caption" value="$(caption)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('send_video.send')}">
      <go method="post" href="/wml/send.video">
        <postfield name="to" value="$(to)"/>
        <postfield name="videoUrl" value="$(videoUrl)"/>
        <postfield name="caption" value="$(caption)"/>
      </go>
    </do>

    <p>
      <a href="/wml/send-menu.wml?to=${encodeURIComponent(
        to
      )}" accesskey="0">${t('send_text.back')}</a>
      <a href="/wml/contacts.wml" accesskey="9">${t('send_text.contacts')}</a>
    </p>
  `;

  sendWml(res, card("send-video", t('send_video.title'), body));
});

// Endpoint per inviare audio
// Text-to-Speech form
app.get("/wml/send.tts.wml", (req, res) => {
  const to = esc(req.query.to || "");

  const ttsStatus = ttsEnabled ? '✓ Local TTS Ready' : '⚠ espeak not installed';

  const body = `
    <p><b>${t('send_tts.title')}</b></p>
    <p><small>${ttsStatus} ${t('send_tts.languages')}</small></p>
    <p>${t('send_menu.to')} <input name="to" title="${t('send_text.recipient')}" value="${to}" size="15"/></p>

    <p>${t('send_tts.message')}</p>
    <input name="text" title="${t('send_tts.message_placeholder')}" value="" size="30" maxlength="500"/>

    <p>${t('send_tts.language')}</p>
    <select name="language" title="Language">
      <option value="en">${t('send_tts.english')}</option>
      <option value="it">${t('send_tts.italian')}</option>
    </select>

    <p>${t('send_tts.voice_message')}</p>
    <select name="ptt" title="Voice">
      <option value="true">${t('send_tts.yes_voice')}</option>
      <option value="false">${t('send_tts.no_audio')}</option>
    </select>

    <p><small>${t('send_tts.max_chars')}<br/>${t('send_tts.engine')}</small></p>

    <p>
      <anchor title="${t('send_tts.send')}">${t('send_tts.send')}
        <go method="post" href="/wml/send.tts">
          <postfield name="to" value="$(to)"/>
          <postfield name="text" value="$(text)"/>
          <postfield name="language" value="$(language)"/>
          <postfield name="ptt" value="$(ptt)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('send_tts.send')}">
      <go method="post" href="/wml/send.tts">
        <postfield name="to" value="$(to)"/>
        <postfield name="text" value="$(text)"/>
        <postfield name="language" value="$(language)"/>
        <postfield name="ptt" value="$(ptt)"/>
      </go>
    </do>

    <p>
      <a href="/wml/send-menu.wml?to=${encodeURIComponent(
        to
      )}" accesskey="0">${t('send_text.back')}</a>
      <a href="/wml/contacts.wml" accesskey="9">${t('send_text.contacts')}</a>
    </p>
  `;

  sendWml(res, card("send-tts", t('send_tts.title'), body));
});

app.get("/wml/send.audio.wml", (req, res) => {
  const to = esc(req.query.to || "");

  const body = `
    <p><b>${t('send_audio.title')}</b></p>
    <p>${t('send_menu.to')} <input name="to" title="${t('send_text.recipient')}" value="${to}" size="15"/></p>

    <p>${t('send_audio.url')}</p>
    <input name="audioUrl" title="Audio URL" value="https://" size="30" maxlength="500"/>

    <p>${t('send_audio.type')}</p>
    <select name="audioType" title="Audio Type">
      <option value="audio/mp3">MP3</option>
      <option value="audio/mp4">MP4</option>
      <option value="audio/ogg">OGG</option>
      <option value="audio/wav">WAV</option>
    </select>

    <p>${t('send_audio.voice_message')}</p>
    <select name="ptt" title="Voice Message">
      <option value="false">${t('send_audio.no')}</option>
      <option value="true">${t('send_audio.yes')}</option>
    </select>

    <p><small>${t('send_audio.max_size')}</small></p>

    <p>
      <anchor title="${t('send_audio.send')}">${t('send_audio.send')}
        <go method="post" href="/wml/send.audio">
          <postfield name="to" value="$(to)"/>
          <postfield name="audioUrl" value="$(audioUrl)"/>
          <postfield name="audioType" value="$(audioType)"/>
          <postfield name="ptt" value="$(ptt)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('send_audio.send')}">
      <go method="post" href="/wml/send.audio">
        <postfield name="to" value="$(to)"/>
        <postfield name="audioUrl" value="$(audioUrl)"/>
        <postfield name="audioType" value="$(audioType)"/>
        <postfield name="ptt" value="$(ptt)"/>
      </go>
    </do>

    <p>
      <a href="/wml/send-menu.wml?to=${encodeURIComponent(
        to
      )}" accesskey="0">${t('send_text.back')}</a>
      <a href="/wml/contacts.wml" accesskey="9">${t('send_text.contacts')}</a>
    </p>
  `;

  sendWml(res, card("send-audio", t('send_audio.title'), body));
});

// Endpoint per inviare documenti
app.get("/wml/send.document.wml", (req, res) => {
  const to = esc(req.query.to || "");

  const body = `
    <p><b>${t('send_document.title')}</b></p>
    <p>${t('send_menu.to')} <input name="to" title="${t('send_text.recipient')}" value="${to}" size="15"/></p>

    <p>${t('send_document.url')}</p>
    <input name="documentUrl" title="Document URL" value="https://" size="30" maxlength="500"/>

    <p>${t('send_document.filename')}</p>
    <input name="fileName" title="File name" value="document.pdf" size="20" maxlength="100"/>

    <p>${t('send_document.mime')}</p>
    <select name="mimeType" title="MIME Type">
      <option value="application/pdf">PDF</option>
      <option value="application/msword">Word</option>
      <option value="application/vnd.ms-excel">Excel</option>
      <option value="application/zip">ZIP</option>
      <option value="text/plain">Text</option>
      <option value="application/octet-stream">Other</option>
    </select>

    <p><small>${t('send_document.max_size')}</small></p>

    <p>
      <anchor title="${t('send_document.send')}">${t('send_document.send')}
        <go method="post" href="/wml/send.document">
          <postfield name="to" value="$(to)"/>
          <postfield name="documentUrl" value="$(documentUrl)"/>
          <postfield name="fileName" value="$(fileName)"/>
          <postfield name="mimeType" value="$(mimeType)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('send_document.send')}">
      <go method="post" href="/wml/send.document">
        <postfield name="to" value="$(to)"/>
        <postfield name="documentUrl" value="$(documentUrl)"/>
        <postfield name="fileName" value="$(fileName)"/>
        <postfield name="mimeType" value="$(mimeType)"/>
      </go>
    </do>

    <p>
      <a href="/wml/send-menu.wml?to=${encodeURIComponent(
        to
      )}" accesskey="0">${t('send_text.back')}</a>
      <a href="/wml/contacts.wml" accesskey="9">${t('send_text.contacts')}</a>
    </p>
  `;

  sendWml(res, card("send-document", t('send_document.title'), body));
});

// ============ STICKER PACK BROWSER ENDPOINTS ============

// Serve local sticker files from stickers/ directory
app.get("/wml/stickers/:pack/:file", async (req, res) => {
  try {
    const pack = (req.params.pack || "").replace(/[^a-zA-Z0-9_\-]/g, "");
    const file = (req.params.file || "").replace(/[^a-zA-Z0-9_.\-]/g, "");
    if (!pack || !file) return res.status(400).send("Invalid request");

    const filePath = path.join(STICKERS_DIR, pack, file);
    // Security: path must be strictly inside STICKERS_DIR (regex already strips slashes so
    // path.join cannot escape, but we keep the check as a defence-in-depth measure)
    const stickersDirNorm = STICKERS_DIR.endsWith(path.sep) ? STICKERS_DIR : STICKERS_DIR + path.sep;
    if (!filePath.startsWith(stickersDirNorm)) return res.status(403).send("Forbidden");

    const ext = path.extname(file).toLowerCase();
    const mimeMap = { ".webp": "image/webp", ".gif": "image/gif", ".jpg": "image/jpeg", ".jpeg": "image/jpeg", ".png": "image/png" };
    const ct = mimeMap[ext] || "application/octet-stream";

    // Read file directly (avoids TOCTOU race of existsSync → sendFile)
    const data = await fs.promises.readFile(filePath);
    res.setHeader("Content-Type", ct);
    res.setHeader("Content-Length", data.length);
    res.setHeader("Cache-Control", "public, max-age=86400"); // local stickers can be cached
    res.send(data);
  } catch (e) {
    if (e.code === "ENOENT") return res.status(404).send("Sticker not found");
    console.error("[Sticker serve]", e.message);
    if (!res.headersSent) res.status(500).send("Error");
  }
});

// List available sticker packs
app.get("/wml/sticker-packs.wml", (req, res) => {
  const to = esc(req.query.to || "");

  let packs = [];
  try {
    if (fs.existsSync(STICKERS_DIR)) {
      packs = fs.readdirSync(STICKERS_DIR).filter(name => {
        try { return fs.statSync(path.join(STICKERS_DIR, name)).isDirectory(); } catch { return false; }
      });
    }
  } catch (e) { /* ignore */ }

  if (packs.length === 0) {
    const anyRunning = [...stickerDownloadStatus.values()].some(s => s.running);
    const body = `
      <p><b>Sticker Packs</b></p>
      ${anyRunning
        ? `<p>${t('stickers.downloading')}</p><p><a href="/wml/sticker-packs.wml?to=${encodeURIComponent(to)}">${t('stickers.refresh')}</a></p>`
        : `<p>${t('stickers.no_packs')}</p>
           <p><a href="/wml/manage-sticker-packs.wml?to=${encodeURIComponent(to)}" accesskey="1">${t('stickers.download_packs')}</a></p>`
      }
      <p><a href="/wml/send.sticker.wml?to=${encodeURIComponent(to)}" accesskey="0">[0] Back</a></p>
    `;
    return sendWml(res, card("sticker-packs", "Sticker Packs", body));
  }

  const packLinks = packs.map((pack, i) => {
    const num = i + 1;
    const key = num <= 9 ? ` accesskey="${num}"` : "";
    // Count stickers in pack
    let count = 0;
    try { count = fs.readdirSync(path.join(STICKERS_DIR, pack)).filter(f => [".webp",".gif",".jpg",".jpeg",".png"].includes(path.extname(f).toLowerCase())).length; } catch {}
    return `<p><a href="/wml/sticker-pack.wml?pack=${encodeURIComponent(pack)}&amp;to=${encodeURIComponent(to)}"${key}>[${num}] ${esc(pack)} (${count})</a></p>`;
  }).join("");

  const body = `
    <p><b>${t('stickers.local_packs')} (${packs.length})</b></p>
    ${packLinks}
    <p><a href="/wml/manage-sticker-packs.wml?to=${encodeURIComponent(to)}" accesskey="7">${t('stickers.manage')}</a></p>
    <p><a href="/wml/send.sticker.wml?to=${encodeURIComponent(to)}" accesskey="0">${t('stickers.back')}</a></p>
  `;
  sendWml(res, card("sticker-packs", t('stickers.title'), body));
});

// Manage / download sticker packs
app.get("/wml/manage-sticker-packs.wml", (req, res) => {
  const to = esc(req.query.to || "");

  const items = BUILTIN_STICKER_PACKS.map((pack, i) => {
    const packDir = path.join(STICKERS_DIR, pack.name);
    let count = 0;
    try { count = fs.existsSync(packDir) ? fs.readdirSync(packDir).filter(f => [".webp",".gif",".jpg",".jpeg",".png"].includes(path.extname(f).toLowerCase())).length : 0; } catch {}
    const status = stickerDownloadStatus.get(pack.name);
    let statusTag = count > 0 ? `OK(${count})` : t('stickers.status_empty');
    if (status?.running) statusTag = t('stickers.status_downloading');
    const num = i + 1;
    const key = num <= 9 ? ` accesskey="${num}"` : "";
    return `<p>${num}. ${esc(pack.name)} [${statusTag}]<br/><a href="/wml/run-download-pack.wml?pack=${encodeURIComponent(pack.name)}&amp;to=${encodeURIComponent(to)}"${key}>${t('stickers.download_btn')}</a></p>`;
  }).join("");

  const body = `
    <p><b>${t('stickers.manage_title')}</b></p>
    ${items}
    <p><a href="/wml/run-download-pack.wml?all=1&amp;to=${encodeURIComponent(to)}" accesskey="9">${t('stickers.download_all')}</a></p>
    <p><a href="/wml/sticker-packs.wml?to=${encodeURIComponent(to)}" accesskey="0">${t('stickers.back')}</a></p>
  `;
  sendWml(res, card("manage-packs", t('stickers.manage_title'), body));
});

// Trigger download of one pack (or all) — synchronous, shows result.
// Protected against concurrent downloads of the same pack via stickerDownloadStatus.
app.get("/wml/run-download-pack.wml", async (req, res) => {
  const to = esc(req.query.to || "");
  const packName = (req.query.pack || "").replace(/[^a-zA-Z0-9_\-]/g, "");
  const all = req.query.all === "1";

  const targets = all
    ? BUILTIN_STICKER_PACKS
    : BUILTIN_STICKER_PACKS.filter(p => p.name === packName);

  if (targets.length === 0) {
    return sendWml(res, card("dl-pack", t('stickers.error'),
      `<p>${t('stickers.pack_not_found')} ${esc(packName)}</p>` +
      `<p><a href="/wml/manage-sticker-packs.wml?to=${encodeURIComponent(to)}" accesskey="0">${t('stickers.back')}</a></p>`));
  }

  // Mark all targets as running BEFORE any await — prevents concurrent requests from
  // starting the same download in parallel (check-then-set in one synchronous step).
  const toRun = [];
  for (const pack of targets) {
    if (getStickerStatus(pack.name).running) continue; // already in progress
    stickerDownloadStatus.set(pack.name, { running: true, done: false, downloaded: 0, errors: 0 });
    toRun.push(pack);
  }

  const results = targets.map(p =>
    getStickerStatus(p.name).running && !toRun.includes(p)
      ? `${p.name}: ${t('stickers.already_running')}`
      : null
  ).filter(Boolean);

  for (const pack of toRun) {
    try {
      const r = await downloadStickerPack(pack.name, pack.query, pack.trending);
      stickerDownloadStatus.set(pack.name, { running: false, done: true, downloaded: r.downloaded, errors: r.errors });
      results.push(`${pack.name}: +${r.downloaded} ${t('stickers.new_stickers')}, ${r.skipped} ${t('stickers.existing')}`);
    } catch (e) {
      stickerDownloadStatus.set(pack.name, { running: false, done: false, downloaded: 0, errors: 1 });
      results.push(`${pack.name}: ${t('stickers.error_prefix')}${e.message}`);
    }
  }

  const body = `
    <p><b>${t('stickers.download_complete')}</b></p>
    ${results.map(r => `<p>${esc(r)}</p>`).join("")}
    <p><a href="/wml/sticker-packs.wml?to=${encodeURIComponent(to)}" accesskey="1">${t('stickers.view_packs')}</a></p>
    <p><a href="/wml/manage-sticker-packs.wml?to=${encodeURIComponent(to)}" accesskey="0">${t('stickers.back')}</a></p>
  `;
  sendWml(res, card("dl-result", t('stickers.title'), body));
});

// Browse stickers within a pack
app.get("/wml/sticker-pack.wml", (req, res) => {
  const to = esc(req.query.to || "");
  const packRaw = req.query.pack || "";
  const pack = packRaw.replace(/[^a-zA-Z0-9_\-]/g, "");
  const page = Math.max(1, parseInt(req.query.page || "1", 10));
  const pageSize = 5;

  const packDir = path.join(STICKERS_DIR, pack);
  let stickers = [];
  try {
    if (fs.existsSync(packDir)) {
      stickers = fs.readdirSync(packDir).filter(f => {
        const ext = path.extname(f).toLowerCase();
        return [".webp", ".gif", ".jpg", ".jpeg", ".png"].includes(ext);
      }).sort();
    }
  } catch (e) { /* ignore */ }

  if (stickers.length === 0) {
    const body = `
      <p><b>Pack: ${esc(pack)}</b></p>
      <p>No stickers found in this pack.</p>
      <p><a href="/wml/sticker-packs.wml?to=${encodeURIComponent(to)}" accesskey="0">[0] Packs</a></p>
    `;
    return sendWml(res, card("sticker-pack", esc(pack), body));
  }

  const totalPages = Math.ceil(stickers.length / pageSize);
  const currentPage = Math.min(page, totalPages);
  const start = (currentPage - 1) * pageSize;
  const pageStickers = stickers.slice(start, start + pageSize);

  const stickerItems = pageStickers.map((fname, i) => {
    const num = start + i + 1;
    const name = path.basename(fname, path.extname(fname));
    const ext = path.extname(fname).toLowerCase();
    const typeTag = ext === ".gif" ? "[GIF]" : ext === ".webp" ? "[WP]" : "[IMG]";
    const key = (i + 1) <= 9 ? ` accesskey="${i + 1}"` : "";
    const quickSend = to
      ? `<anchor title="Quick Send">[Quick]
        <go method="post" href="/wml/send.sticker">
          <postfield name="to" value="${to}"/>
          <postfield name="pack" value="${esc(pack)}"/>
          <postfield name="file" value="${esc(fname)}"/>
        </go>
      </anchor>`
      : "";
    return `<p>${num}. ${esc(name)} ${typeTag}<br/><a href="/wml/send.sticker.wml?to=${encodeURIComponent(to)}&amp;pack=${encodeURIComponent(pack)}&amp;file=${encodeURIComponent(fname)}"${key}>[Send]</a> ${quickSend}</p>`;
  }).join("");

  let pagination = "";
  if (totalPages > 1) {
    pagination = "<p>";
    if (currentPage > 1)
      pagination += `<a href="/wml/sticker-pack.wml?pack=${encodeURIComponent(pack)}&amp;to=${encodeURIComponent(to)}&amp;page=${currentPage - 1}">[Prev]</a> `;
    pagination += `Pg ${currentPage}/${totalPages}`;
    if (currentPage < totalPages)
      pagination += ` <a href="/wml/sticker-pack.wml?pack=${encodeURIComponent(pack)}&amp;to=${encodeURIComponent(to)}&amp;page=${currentPage + 1}">[Next]</a>`;
    pagination += "</p>";
  }

  const body = `
    <p><b>${esc(pack)}</b> (${stickers.length})</p>
    ${stickerItems}
    ${pagination}
    <p><a href="/wml/sticker-packs.wml?to=${encodeURIComponent(to)}" accesskey="0">[0] Packs</a></p>
  `;
  sendWml(res, card("sticker-pack", esc(pack), body));
});

// ============ GIPHY GIF STICKER SEARCH ============

// Search form
app.get("/wml/gif-search.wml", (req, res) => {
  if (STICKER_PROVIDER === "openmoji") {
    return sendWml(
      res,
      resultCard(
        "OpenMoji Only",
        ["Online GIF search is disabled. Use OpenMoji local packs."],
        `/wml/sticker-packs.wml?to=${encodeURIComponent(req.query.to || "")}`,
        false
      )
    );
  }
  const to = esc(req.query.to || "");
  const body = `
    <p><b>GIF Sticker Search</b></p>
    <p>To: ${to || "(not set)"}</p>
    <p>
      <input name="q" title="Search" value="" size="20" maxlength="80"/>
    </p>
    <p>
      <anchor title="Search">Search
        <go href="/wml/gif-results.wml">
          <postfield name="q" value="$(q)"/>
          <postfield name="to" value="${to}"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.search')}">
      <go href="/wml/gif-results.wml">
        <postfield name="q" value="$(q)"/>
        <postfield name="to" value="${to}"/>
      </go>
    </do>
    <p><a href="/wml/gif-results.wml?trending=1&amp;to=${encodeURIComponent(req.query.to || "")}" accesskey="1">[1] Trending Stickers</a></p>
    <p><a href="/wml/sticker-packs.wml?to=${encodeURIComponent(req.query.to || "")}" accesskey="0">[0] Local Packs</a></p>
  `;
  sendWml(res, card("gif-search", "GIF Search", body));
});

// Search results from Giphy
app.get("/wml/gif-results.wml", async (req, res) => {
  if (STICKER_PROVIDER === "openmoji") {
    return sendWml(
      res,
      resultCard(
        "OpenMoji Only",
        ["Online GIF results are disabled. Use OpenMoji local packs."],
        `/wml/sticker-packs.wml?to=${encodeURIComponent(req.query.to || "")}`,
        false
      )
    );
  }
  const q = (req.query.q || "").trim();
  const trending = req.query.trending === "1";
  const page = Math.max(1, parseInt(req.query.page || "1", 10));
  const limit = 5;
  const offset = (page - 1) * limit;

  try {
    let apiUrl;
    if (trending || !q) {
      apiUrl = `https://api.giphy.com/v1/stickers/trending?api_key=${GIPHY_API_KEY}&limit=${limit}&offset=${offset}&rating=g`;
    } else {
      apiUrl = `https://api.giphy.com/v1/stickers/search?api_key=${GIPHY_API_KEY}&q=${encodeURIComponent(q)}&limit=${limit}&offset=${offset}&rating=g&lang=it`;
    }

    const resp = await axios.get(apiUrl, { timeout: 10000 });
    const giphyData = resp.data;
    const stickers = giphyData.data || [];
    const totalCount = giphyData.pagination?.total_count || 0;
    const totalPages = Math.min(Math.ceil(totalCount / limit), 20); // cap at 20 pages

    if (stickers.length === 0) {
      const body = `
        <p><b>No results</b></p>
        <p>Query: ${esc(q) || "trending"}</p>
        <p>Try a different search.</p>
        <p><a href="/wml/gif-search.wml?to=${encodeURIComponent(req.query.to || "")}" accesskey="0">[0] Back</a></p>
      `;
      return sendWml(res, card("gif-results", "GIF Results", body));
    }

    const items = stickers.flatMap((s, i) => {
      const gifUrl = s.images?.downsized?.url || s.images?.fixed_height_small?.url || s.images?.original?.url || "";
      if (!gifUrl) return []; // skip stickers without a usable URL
      const title = String(s.title || s.slug || "Sticker").replace(/\+/g, " ").substring(0, 30);
      const sizeBytes = parseInt(s.images?.downsized?.size || s.images?.original?.size || "0", 10);
      const sizeKb = sizeBytes > 0 ? `${Math.round(sizeBytes / 1024)}KB` : "";
      const num = offset + i + 1;
      const key = (i + 1) <= 9 ? ` accesskey="${i + 1}"` : "";
      return [`<p>${num}. ${esc(title)}${sizeKb ? " " + sizeKb : ""}<br/><a href="/wml/gif-confirm.wml?to=${encodeURIComponent(req.query.to || "")}&amp;url=${encodeURIComponent(gifUrl)}&amp;title=${encodeURIComponent(title)}"${key}>[Send]</a></p>`];
    }).join("");

    let pagination = "";
    if (totalPages > 1) {
      pagination = "<p>";
      if (page > 1) {
        const prev = `/wml/gif-results.wml?q=${encodeURIComponent(q)}&to=${encodeURIComponent(req.query.to || "")}&page=${page - 1}${trending ? "&trending=1" : ""}`;
        pagination += `<a href="${prev}">[Prev]</a> `;
      }
      pagination += `Pg ${page}/${totalPages}`;
      if (page < totalPages) {
        const next = `/wml/gif-results.wml?q=${encodeURIComponent(q)}&to=${encodeURIComponent(req.query.to || "")}&page=${page + 1}${trending ? "&trending=1" : ""}`;
        pagination += ` <a href="${next}">[Next]</a>`;
      }
      pagination += "</p>";
    }

    const titleLine = trending ? "Trending Stickers" : `Results: ${esc(q)}`;
    const body = `
      <p><b>${titleLine}</b></p>
      <p>${totalCount} found</p>
      ${items}
      ${pagination}
      <p><a href="/wml/gif-search.wml?to=${encodeURIComponent(req.query.to || "")}" accesskey="0">[0] Search</a></p>
    `;
    sendWml(res, card("gif-results", "GIF Results", body));
  } catch (err) {
    const body = `
      <p><b>Search Error</b></p>
      <p>${esc(err.message || "Connection failed")}</p>
      <p>Check internet connection.</p>
      <p><a href="/wml/gif-search.wml?to=${encodeURIComponent(req.query.to || "")}" accesskey="0">[0] Back</a></p>
    `;
    sendWml(res, card("gif-results", "GIF Error", body));
  }
});

// Confirm and send a Giphy GIF sticker
app.get("/wml/gif-confirm.wml", (req, res) => {
  if (STICKER_PROVIDER === "openmoji") {
    return sendWml(
      res,
      resultCard(
        "OpenMoji Only",
        ["GIF confirm is disabled. Use OpenMoji local packs."],
        `/wml/sticker-packs.wml?to=${encodeURIComponent(req.query.to || "")}`,
        false
      )
    );
  }
  const to = esc(req.query.to || "");
  const url = esc(req.query.url || "");
  const title = esc(req.query.title || "Sticker");
  const body = `
    <p><b>Send GIF Sticker?</b></p>
    <p>To: ${to || "(not set)"}</p>
    <p>Sticker: ${title}</p>
    <p>
      <anchor title="Send">Send
        <go method="post" href="/wml/send.sticker">
          <postfield name="to" value="${to}"/>
          <postfield name="stickerUrl" value="${url}"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.send')}">
      <go method="post" href="/wml/send.sticker">
        <postfield name="to" value="${to}"/>
        <postfield name="stickerUrl" value="${url}"/>
      </go>
    </do>
    <p><a href="/wml/gif-search.wml?to=${encodeURIComponent(req.query.to || "")}" accesskey="0">[0] Back</a></p>
  `;
  sendWml(res, card("gif-confirm", "Confirm GIF", body));
});

// Send Sticker form (URL or from local pack)
app.get("/wml/send.sticker.wml", (req, res) => {
  const to = esc(req.query.to || userSettings.lastStickerTo || "");
  const pack = esc(req.query.pack || "");
  const file = esc(req.query.file || "");

  // If a local sticker was pre-selected from the browser, show confirmation
  if (pack && file) {
    const name = path.basename(file, path.extname(file));
    const ext = path.extname(file).toLowerCase();
    const typeLabel = ext === ".gif" ? "GIF (animated)" : ext === ".webp" ? "WebP" : ext.replace(".", "").toUpperCase();
    const body = `
      <p><b>Send Local Sticker</b></p>
      <p>To: ${to || "(not set)"}</p>
      <p>Pack: ${pack}</p>
      <p>Sticker: ${esc(name)}</p>
      <p>Format: ${typeLabel}</p>
      <p>
        <anchor title="Send">Send
          <go method="post" href="/wml/send.sticker">
            <postfield name="to" value="${to}"/>
            <postfield name="pack" value="${pack}"/>
            <postfield name="file" value="${file}"/>
          </go>
        </anchor>
      </p>
      <do type="accept" label="${t('common.send')}">
        <go method="post" href="/wml/send.sticker">
          <postfield name="to" value="${to}"/>
          <postfield name="pack" value="${pack}"/>
          <postfield name="file" value="${file}"/>
        </go>
      </do>
      <p>
        <a href="/wml/sticker-pack.wml?pack=${encodeURIComponent(req.query.pack || "")}&amp;to=${encodeURIComponent(req.query.to || "")}" accesskey="0">[0] Back</a>
        <a href="/wml/sticker-packs.wml?to=${encodeURIComponent(req.query.to || "")}" accesskey="9">[9] Packs</a>
      </p>
    `;
    return sendWml(res, card("send-sticker", "Confirm Sticker", body));
  }

  const body = `
    <p><b>Send Sticker</b></p>
    <p>To: <input name="to" title="Recipient" value="${to}" size="15"/></p>
    ${to ? "" : `<p><small>No recipient selected. Open a chat first or choose from contacts.</small></p><p><a href="/wml/contacts.wml" accesskey="9">[9] Contacts</a></p>`}

    <p>Option 1 - OpenMoji packs:</p>
    <p><a href="/wml/sticker-packs.wml?to=${encodeURIComponent(req.query.to || to || "")}" accesskey="1">[1] Local Packs</a></p>

    <p>Option 2 - Download/Update OpenMoji packs:</p>
    <p><a href="/wml/manage-sticker-packs.wml?to=${encodeURIComponent(req.query.to || to || "")}" accesskey="2">[2] Manage Packs</a></p>

    <p>
      <a href="/wml/send-menu.wml?to=${encodeURIComponent(req.query.to || "")}" accesskey="0">[0] Back</a>
      <a href="/wml/contacts.wml" accesskey="9">[9] Contacts</a>
    </p>
  `;

  sendWml(res, card("send-sticker", "Send Sticker", body));
});

// Endpoint per inviare posizione
app.get("/wml/send.location.wml", (req, res) => {
  const to = esc(req.query.to || "");

  const body = `
    <p><b>Send Location</b></p>
    <p>To: <input name="to" title="Recipient" value="${to}" size="15"/></p>
    
    <p>Latitude:</p>
    <input name="latitude" title="Latitude" value="41.9028" size="15" maxlength="20"/>
    
    <p>Longitude:</p>
    <input name="longitude" title="Longitude" value="12.4964" size="15" maxlength="20"/>
    
    <p>Location Name (optional):</p>
    <input name="name" title="Location name" value="" size="20" maxlength="100"/>
    
    <p><small>Example: Rome, Italy</small></p>
    
    <p>
      <anchor title="Send">Send
        <go method="post" href="/wml/send.location">
          <postfield name="to" value="$(to)"/>
          <postfield name="latitude" value="$(latitude)"/>
          <postfield name="longitude" value="$(longitude)"/>
          <postfield name="name" value="$(name)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.send')}">
      <go method="post" href="/wml/send.location">
        <postfield name="to" value="$(to)"/>
        <postfield name="latitude" value="$(latitude)"/>
        <postfield name="longitude" value="$(longitude)"/>
        <postfield name="name" value="$(name)"/>
      </go>
    </do>

    <p>
      <a href="/wml/send-menu.wml?to=${encodeURIComponent(
        to
      )}" accesskey="0">[0] Back</a>
      <a href="/wml/contacts.wml" accesskey="9">[9] Contacts</a>
    </p>
  `;

  sendWml(res, card("send-location", "Send Location", body));
});

// Endpoint per inviare contatti
app.get("/wml/send.contact.wml", (req, res) => {
  const to = esc(req.query.to || "");

  const body = `
    <p><b>Send Contact</b></p>
    <p>To: <input name="to" title="Recipient" value="${to}" size="15"/></p>
    
    <p>Contact Name:</p>
    <input name="contactName" title="Contact name" value="" size="20" maxlength="50"/>
    
    <p>Phone Number:</p>
    <input name="phoneNumber" title="Phone number" value="" size="15" maxlength="20"/>
    
    <p>Organization (optional):</p>
    <input name="organization" title="Organization" value="" size="20" maxlength="50"/>
    
    <p>Email (optional):</p>
    <input name="email" title="Email" value="" size="20" maxlength="100"/>
    
    <p><small>Format: +39XXXXXXXXXX</small></p>
    
    <p>
      <anchor title="Send">Send
        <go method="post" href="/wml/send.contact">
          <postfield name="to" value="$(to)"/>
          <postfield name="contactName" value="$(contactName)"/>
          <postfield name="phoneNumber" value="$(phoneNumber)"/>
          <postfield name="organization" value="$(organization)"/>
          <postfield name="email" value="$(email)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.send')}">
      <go method="post" href="/wml/send.contact">
        <postfield name="to" value="$(to)"/>
        <postfield name="contactName" value="$(contactName)"/>
        <postfield name="phoneNumber" value="$(phoneNumber)"/>
        <postfield name="organization" value="$(organization)"/>
        <postfield name="email" value="$(email)"/>
      </go>
    </do>

    <p>
      <a href="/wml/send-menu.wml?to=${encodeURIComponent(
        to
      )}" accesskey="0">[0] Back</a>
      <a href="/wml/contacts.wml" accesskey="9">[9] Contacts</a>
    </p>
  `;

  sendWml(res, card("send-contact", "Send Contact", body));
});

// Endpoint per inviare sondaggi
app.get("/wml/send.poll.wml", (req, res) => {
  const to = esc(req.query.to || "");

  const body = `
    <p><b>Send Poll</b></p>
    <p>To: <input name="to" title="Recipient" value="${to}" size="15"/></p>
    
    <p>Poll Question:</p>
    <input name="pollName" title="Poll question" value="" size="25" maxlength="100"/>
    
    <p>Option 1:</p>
    <input name="option1" title="Option 1" value="" size="20" maxlength="50"/>
    
    <p>Option 2:</p>
    <input name="option2" title="Option 2" value="" size="20" maxlength="50"/>
    
    <p>Option 3 (optional):</p>
    <input name="option3" title="Option 3" value="" size="20" maxlength="50"/>
    
    <p>Option 4 (optional):</p>
    <input name="option4" title="Option 4" value="" size="20" maxlength="50"/>
    
    <p>Selectable Answers:</p>
    <select name="selectableCount" title="Selectable answers">
      <option value="1">1 answer</option>
      <option value="2">2 answers</option>
      <option value="3">3 answers</option>
      <option value="4">4 answers</option>
    </select>
    
    <p><small>Min 2 options, max 12 options per poll</small></p>
    
    <p>
      <anchor title="Send">Send
        <go method="post" href="/wml/send.poll">
          <postfield name="to" value="$(to)"/>
          <postfield name="pollName" value="$(pollName)"/>
          <postfield name="option1" value="$(option1)"/>
          <postfield name="option2" value="$(option2)"/>
          <postfield name="option3" value="$(option3)"/>
          <postfield name="option4" value="$(option4)"/>
          <postfield name="selectableCount" value="$(selectableCount)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.send')}">
      <go method="post" href="/wml/send.poll">
        <postfield name="to" value="$(to)"/>
        <postfield name="pollName" value="$(pollName)"/>
        <postfield name="option1" value="$(option1)"/>
        <postfield name="option2" value="$(option2)"/>
        <postfield name="option3" value="$(option3)"/>
        <postfield name="option4" value="$(option4)"/>
        <postfield name="selectableCount" value="$(selectableCount)"/>
      </go>
    </do>

    <p>
      <a href="/wml/send-menu.wml?to=${encodeURIComponent(
        to
      )}" accesskey="0">[0] Back</a>
      <a href="/wml/contacts.wml" accesskey="9">[9] Contacts</a>
    </p>
  `;

  sendWml(res, card("send-poll", "Send Poll", body));
});

// POST handlers per ogni tipo di messaggio
// WML Media Send Routes — Pure SSR, server downloads from URL then sends to WhatsApp.
// Nokia submits WML form -> server fetches media -> server sends to WhatsApp -> WML result page.
//
// TIME: O(N) where N = media file size — dominated by network I/O (download + upload)
// SPACE: O(N) — single arraybuffer in memory, no redundant copies

app.post("/wml/send.image", async (req, res) => {
  try {
    const { to, imageUrl, caption } = req.body;
    if (!sock) throw new Error("Not connected");
    if (!imageUrl || imageUrl === 'https://') throw new Error("No image URL provided");

    // O(N) — single HTTP GET, arraybuffer avoids string encoding overhead
    const response = await axios.get(imageUrl, {
      responseType: "arraybuffer",
      timeout: 60000,
      maxContentLength: 50 * 1024 * 1024,
      maxBodyLength: 50 * 1024 * 1024
    });
    // O(N) — Baileys encrypts + uploads to WhatsApp servers
    const result = await sock.sendMessage(formatJid(to), {
      image: response.data,
      caption: caption || undefined,
    });

    sendWml(res, resultCard("Image Sent", [
      `To: ${jidFriendly(to)}`,
      `Caption: ${caption || "No caption"}`,
      `ID: ${result?.key?.id || "Unknown"}`,
    ], `/wml/send-menu.wml?to=${encodeURIComponent(to)}`));
  } catch (error) {
    sendWml(res, resultCard("Send Failed", [error.message || "Failed to send image"], "/wml/send.image.wml"));
  }
});

app.post("/wml/send.video", async (req, res) => {
  try {
    const { to, videoUrl, caption } = req.body;
    if (!sock) throw new Error("Not connected");
    if (!videoUrl || videoUrl === 'https://') throw new Error("No video URL provided");

    // O(N) — single HTTP GET
    const response = await axios.get(videoUrl, {
      responseType: "arraybuffer",
      timeout: 120000,
      maxContentLength: 100 * 1024 * 1024,
      maxBodyLength: 100 * 1024 * 1024
    });
    // O(N) — direct buffer pass-through, no conversion
    const result = await sock.sendMessage(formatJid(to), {
      video: response.data,
      caption: caption || undefined,
    });

    sendWml(res, resultCard("Video Sent", [
      `To: ${jidFriendly(to)}`,
      `Caption: ${caption || "No caption"}`,
      `ID: ${result?.key?.id || "Unknown"}`,
    ], `/wml/send-menu.wml?to=${encodeURIComponent(to)}`));
  } catch (error) {
    sendWml(res, resultCard("Send Failed", [error.message || "Failed to send video"], "/wml/send.video.wml"));
  }
});

// Send TTS audio message
app.post("/wml/send.tts", async (req, res) => {
  try {
    const { to, text, language = "en", ptt = "true" } = req.body;

    if (!sock) throw new Error("Not connected");
    if (!text || text.trim().length === 0) {
      throw new Error("Please enter text to convert to speech");
    }

    console.log(`TTS request: "${text}" in ${language} to ${to}`);

    // Convert text to speech using local espeak (returns WAV)
    const audioBuffer = await textToSpeech(text, language);

    console.log(`TTS audio generated: ${audioBuffer.length} bytes (WAV from espeak)`);

    // Convert WAV to OGG Opus for WhatsApp compatibility
    console.log('Converting WAV to OGG Opus...');
    const oggBuffer = await convertWavToOgg(audioBuffer);
    console.log(`Converted to OGG: ${oggBuffer.length} bytes`);

    // Send as WhatsApp audio message
    const result = await sock.sendMessage(formatJid(to), {
      audio: oggBuffer,
      ptt: ptt === "true",
      mimetype: "audio/ogg; codecs=opus",
    });

    sendWml(
      res,
      resultCard(
        "Voice Message Sent",
        [
          `To: ${jidFriendly(to)}`,
          `Text: "${text.substring(0, 50)}${text.length > 50 ? "..." : ""}"`,
          `Language: ${language}`,
          `Type: ${ptt === "true" ? "Voice Note (PTT)" : "Audio File"}`,
          `ID: ${result?.key?.id || "Unknown"}`,
        ],
        `/wml/send-menu.wml?to=${encodeURIComponent(to)}`
      )
    );
  } catch (error) {
    console.error("TTS send error:", error);
    sendWml(
      res,
      resultCard(
        "Send Failed",
        [error.message || "Failed to send voice message"],
        "/wml/send.tts.wml"
      )
    );
  }
});

// O(N) time, O(N) space — server downloads audio from URL, sends to WhatsApp
app.post("/wml/send.audio", async (req, res) => {
  try {
    const { to, audioUrl, audioType = "audio/mp4", ptt = "false" } = req.body;
    if (!sock) throw new Error("Not connected");
    if (!audioUrl || audioUrl === 'https://') throw new Error("No audio URL provided");

    // O(N) — single arraybuffer download, no intermediate string allocation
    const response = await axios.get(audioUrl, {
      responseType: "arraybuffer",
      timeout: 60000,
      maxContentLength: 50 * 1024 * 1024,
      maxBodyLength: 50 * 1024 * 1024
    });
    // O(N) — direct buffer pass-through to Baileys
    const result = await sock.sendMessage(formatJid(to), {
      audio: response.data,
      ptt: ptt === "true",  // O(1) string comparison
      mimetype: audioType,
    });

    sendWml(res, resultCard("Audio Sent", [
      `To: ${jidFriendly(to)}`,
      `Type: ${audioType}`,
      `Voice Message: ${ptt === "true" ? "Yes" : "No"}`,
      `ID: ${result?.key?.id || "Unknown"}`,
    ], `/wml/send-menu.wml?to=${encodeURIComponent(to)}`));
  } catch (error) {
    sendWml(res, resultCard("Send Failed", [error.message || "Failed to send audio"], "/wml/send.audio.wml"));
  }
});

// O(N) time, O(N) space — server downloads document from URL, sends to WhatsApp
app.post("/wml/send.document", async (req, res) => {
  try {
    const { to, documentUrl, fileName, mimeType } = req.body;
    if (!sock) throw new Error("Not connected");
    if (!documentUrl || documentUrl === 'https://') throw new Error("No document URL provided");

    // O(N) — single arraybuffer download
    const response = await axios.get(documentUrl, {
      responseType: "arraybuffer",
      timeout: 120000,
      maxContentLength: 100 * 1024 * 1024,
      maxBodyLength: 100 * 1024 * 1024
    });
    // O(N) — direct buffer pass-through
    const result = await sock.sendMessage(formatJid(to), {
      document: response.data,
      fileName: fileName || "document",
      mimetype: mimeType || "application/octet-stream",
    });

    sendWml(
      res,
      resultCard(
        "Document Sent",
        [
          `To: ${jidFriendly(to)}`,
          `File: ${fileName || "document"}`,
          `Type: ${mimeType || "application/octet-stream"}`,
          `ID: ${result?.key?.id || "Unknown"}`,
        ],
        `/wml/send-menu.wml?to=${encodeURIComponent(to)}`
      )
    );
  } catch (error) {
    sendWml(
      res,
      resultCard(
        "Send Failed",
        [error.message || "Failed to send document"],
        "/wml/send.document.wml"
      )
    );
  }
});

// Convert any image buffer to WebP (for sending as sticker).
// Returns the WebP buffer, or throws with a descriptive message.
async function toStickerWebp(rawBuffer, hint = "image") {
  if (!rawBuffer || rawBuffer.length === 0) throw new Error(`Empty buffer for ${hint}`);

  // Detect animated GIF by checking first 6 bytes (GIF89a has animation capability)
  const isGifBuf = rawBuffer.length >= 6 &&
    rawBuffer[0] === 0x47 && rawBuffer[1] === 0x49 && rawBuffer[2] === 0x46; // "GIF"

  try {
    const meta = await sharp(rawBuffer, isGifBuf ? { animated: true } : {}).metadata();
    const isAnimated = isGifBuf && meta.pages > 1;
    return await sharp(rawBuffer, isAnimated ? { animated: true } : {})
      .webp({ quality: 80 })
      .toBuffer();
  } catch (e) {
    // Log clearly so ENOENT/format errors are visible in server logs
    logger.warn(`[Sticker] sharp conversion failed for ${hint}: ${e.message}`);
    throw new Error(`Cannot convert ${hint} to WebP: ${e.message}`);
  }
}

app.post("/wml/send.sticker", async (req, res) => {
  try {
    const { to, stickerUrl, pack, file } = req.body;
    if (!sock) throw new Error("Not connected");
    if (!to) throw new Error("No recipient specified");
    const toJid = formatJid(to);
    if (!toJid) throw new Error("Invalid recipient");

    let stickerBuffer;
    let sourceLabel;

    if (pack && file) {
      // ---- Local sticker from pack ----
      const safePack = (pack || "").replace(/[^a-zA-Z0-9_\-]/g, "");
      const safeFile = (file || "").replace(/[^a-zA-Z0-9_.\-]/g, "");
      if (!safePack || !safeFile) throw new Error("Invalid sticker pack/file name");

      const filePath = path.join(STICKERS_DIR, safePack, safeFile);
      const stickersDirNorm = STICKERS_DIR.endsWith(path.sep) ? STICKERS_DIR : STICKERS_DIR + path.sep;
      if (!filePath.startsWith(stickersDirNorm)) throw new Error("Invalid sticker path");

      // Read file directly — no existsSync (avoids TOCTOU race condition)
      let rawBuffer;
      try {
        rawBuffer = await fs.promises.readFile(filePath);
      } catch (e) {
        if (e.code === "ENOENT") throw new Error(`Sticker file not found: ${safeFile}`);
        throw new Error(`Cannot read sticker file: ${e.message}`);
      }

      const ext = path.extname(safeFile).toLowerCase();
      if (ext === ".webp") {
        stickerBuffer = rawBuffer; // native — send directly
      } else {
        // GIF, JPG, PNG → WebP
        stickerBuffer = await toStickerWebp(rawBuffer, safeFile);
      }
      sourceLabel = `Pack: ${safePack} / ${path.basename(safeFile, ext)}`;

    } else {
      // ---- Remote URL sticker ----
      const url = (stickerUrl || "").trim();
      if (!url || url === "https://") throw new Error("No sticker URL provided");

      let rawBuf;
      try {
        const response = await axios.get(url, {
          responseType: "arraybuffer",
          timeout: 60000,
          maxContentLength: 10 * 1024 * 1024,
          maxBodyLength: 10 * 1024 * 1024,
        });
        rawBuf = Buffer.from(response.data);
        if (!rawBuf || rawBuf.length === 0) throw new Error("Empty response from URL");
      } catch (e) {
        throw new Error(`Download failed: ${e.message}`);
      }

      // Detect WebP by magic bytes (52 49 46 46 … 57 45 42 50)
      const isWebp = rawBuf.length > 12 &&
        rawBuf[0] === 0x52 && rawBuf[1] === 0x49 && rawBuf[2] === 0x46 && rawBuf[3] === 0x46 &&
        rawBuf[8] === 0x57 && rawBuf[9] === 0x45 && rawBuf[10] === 0x42 && rawBuf[11] === 0x50;

      if (isWebp) {
        stickerBuffer = rawBuf; // already WebP
      } else {
        stickerBuffer = await toStickerWebp(rawBuf, "url-sticker");
      }
      sourceLabel = "URL";
    }

    const result = await sock.sendMessage(toJid, { sticker: stickerBuffer });
    userSettings.lastStickerTo = toJid;
    saveSettings();

    sendWml(
      res,
      resultCard(
        "Sticker Sent",
        [`To: ${jidFriendly(toJid)}`, sourceLabel, `ID: ${result?.key?.id || "Unknown"}`],
        `/wml/send-menu.wml?to=${encodeURIComponent(toJid)}`
      )
    );
  } catch (error) {
    logger.error("[send.sticker]", error.message);
    sendWml(
      res,
      resultCard(
        "Send Failed",
        [error.message || "Failed to send sticker"],
        "/wml/send.sticker.wml"
      )
    );
  }
});

app.post("/wml/send.location", async (req, res) => {
  try {
    const { to, latitude, longitude, name } = req.body;
    if (!sock) throw new Error("Not connected");

    const result = await sock.sendMessage(formatJid(to), {
      location: {
        degreesLatitude: parseFloat(latitude),
        degreesLongitude: parseFloat(longitude),
        name,
      },
    });

    sendWml(
      res,
      resultCard(
        "Location Sent",
        [
          `To: ${jidFriendly(to)}`,
          `Location: ${latitude}, ${longitude}`,
          `Name: ${name || "Unnamed location"}`,
          `ID: ${result?.key?.id || "Unknown"}`,
        ],
        `/wml/send-menu.wml?to=${encodeURIComponent(to)}`
      )
    );
  } catch (error) {
    sendWml(
      res,
      resultCard(
        "Send Failed",
        [error.message || "Failed to send location"],
        "/wml/send.location.wml"
      )
    );
  }
});

app.post("/wml/send.contact", async (req, res) => {
  try {
    const { to, contactName, phoneNumber, organization, email } = req.body;
    if (!sock) throw new Error("Not connected");

    const vcard = `BEGIN:VCARD\nVERSION:3.0\nFN:${contactName}\nTEL;type=CELL:${phoneNumber}\n${
      organization ? `ORG:${organization}\n` : ""
    }${email ? `EMAIL:${email}\n` : ""}END:VCARD`;

    const result = await sock.sendMessage(formatJid(to), {
      contacts: {
        displayName: contactName,
        contacts: [
          {
            displayName: contactName,
            vcard,
          },
        ],
      },
    });

    sendWml(
      res,
      resultCard(
        "Contact Sent",
        [
          `To: ${jidFriendly(to)}`,
          `Contact: ${contactName}`,
          `Phone: ${phoneNumber}`,
          `ID: ${result?.key?.id || "Unknown"}`,
        ],
        `/wml/send-menu.wml?to=${encodeURIComponent(to)}`
      )
    );
  } catch (error) {
    sendWml(
      res,
      resultCard(
        "Send Failed",
        [error.message || "Failed to send contact"],
        "/wml/send.contact.wml"
      )
    );
  }
});

app.post("/wml/send.poll", async (req, res) => {
  try {
    const {
      to,
      pollName,
      option1,
      option2,
      option3,
      option4,
      selectableCount,
    } = req.body;
    if (!sock) throw new Error("Not connected");

    const options = [option1, option2];
    if (option3) options.push(option3);
    if (option4) options.push(option4);

    const result = await sock.sendMessage(formatJid(to), {
      poll: {
        name: pollName,
        values: options,
        selectableCount: Math.min(parseInt(selectableCount, 10) || 1, options.length),
      },
    });

    sendWml(
      res,
      resultCard(
        "Poll Sent",
        [
          `To: ${jidFriendly(to)}`,
          `Question: ${pollName}`,
          `Options: ${options.length}`,
          `Selectable: ${selectableCount}`,
          `ID: ${result?.key?.id || "Unknown"}`,
        ],
        `/wml/send-menu.wml?to=${encodeURIComponent(to)}`
      )
    );
  } catch (error) {
    sendWml(
      res,
      resultCard(
        "Send Failed",
        [error.message || "Failed to send poll"],
        "/wml/send.poll.wml"
      )
    );
  }
});

app.get("/wml/groups.search.wml", async (req, res) => {
  try {
    if (!sock) throw new Error("Not connected");

    // Query di ricerca
    const query = (req.query.q || "").toLowerCase().trim();
    if (!query) throw new Error("No search query provided");

    // Parametri di paginazione
    const page = parseInt(req.query.page) || 1;
    const limit = 3;
    const offset = (page - 1) * limit;

    // Prendo tutti i gruppi e filtro per nome
    const groups = await sock.groupFetchAllParticipating();
    const groupList = Object.values(groups)
      .filter((g) => (g?.subject || "").toLowerCase().includes(query))
      .sort((a, b) => {
        // Simple < > comparison is 10-20x faster than localeCompare
        const sa = (a?.subject || '').toLowerCase(), sb = (b?.subject || '').toLowerCase();
        return sa < sb ? 1 : sa > sb ? -1 : 0;
      });

    const totalGroups = groupList.length;
    const totalPages = Math.max(1, Math.ceil(totalGroups / limit));
    const paginatedGroups = groupList.slice(offset, offset + limit);

    // Escape WML
    // Uses global escWml — single-pass O(L) instead of O(5L)

    // Lista risultati
    const list =
      paginatedGroups
        .map((g, idx) => {
          const globalIdx = offset + idx;
          const memberCount = g?.participants?.length || 0;
          return `<p><b>${globalIdx + 1}.</b> ${escWml(
            g.subject || "Unnamed Group"
          )}<br/>
        <small>${memberCount} members | ${escWml(
            g.id.slice(-8)
          )}...</small><br/>
        <a href="/wml/chat.wml?jid=${encodeURIComponent(
          g.id
        )}&amp;limit=3">[Chat]</a>
      </p>`;
        })
        .join("") ||
      `<p>No groups found matching "<i>${escWml(query)}</i>".</p>`;

    // Controlli paginazione
    let paginationControls = `<p><b>${t('common.pages')}</b><br/>`;
    if (page > 1) {
      paginationControls += `<a href="/wml/groups.search.wml?q=${encodeURIComponent(
        query
      )}&amp;page=1">[First]</a> `;
      paginationControls += `<a href="/wml/groups.search.wml?q=${encodeURIComponent(
        query
      )}&amp;page=${page - 1}">[&lt;]</a> `;
    }

    const startPage = Math.max(1, page - 2);
    const endPage = Math.min(totalPages, page + 2);

    for (let i = startPage; i <= endPage; i++) {
      if (i === page) {
        paginationControls += `<b>[${i}]</b> `;
      } else {
        paginationControls += `<a href="/wml/groups.search.wml?q=${encodeURIComponent(
          query
        )}&amp;page=${i}">[${i}]</a> `;
      }
    }

    if (page < totalPages) {
      paginationControls += `<a href="/wml/groups.search.wml?q=${encodeURIComponent(
        query
      )}&amp;page=${page + 1}">[&gt;]</a> `;
      paginationControls += `<a href="/wml/groups.search.wml?q=${encodeURIComponent(
        query
      )}&amp;page=${totalPages}">[Last]</a>`;
    }

    paginationControls += `<br/><small>Page ${page} of ${totalPages} (${totalGroups} results)</small></p>`;

    // Body
    const body = `
      <p><b>Search results for: "${escWml(query)}"</b></p>
      ${list}
      ${paginationControls}
      <p><a href="/wml/groups.wml">[Back to Groups]</a></p>
      <p>
        <a href="/wml/home.wml">[Home]</a> 
        <a href="/wml/chats.wml">[Chats]</a> 
        <a href="/wml/contacts.wml">[Contacts]</a>
      </p>`;

    const wmlOutput = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
  <head>
    <meta http-equiv="Cache-Control" content="no-cache, no-store"/>
  </head>
  <card id="search" title="Group Search">
    ${body}
  </card>
</wml>`;

    sendRawWmlAware(res, wmlOutput);
  } catch (e) {
    const errorWml = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
  <card id="error" title="Error">
    <p><b>Error:</b></p>
    <p>${e.message || "Failed to search groups"}</p>
    <p><a href="/wml/groups.wml">[Back to Groups]</a></p>
  </card>
</wml>`;

    sendRawWmlAware(res, errorWml);
  }
});

app.get("/wml/groups.wml", async (req, res) => {
  try {
    if (!sock) throw new Error("Not connected");

    // Parametri di paginazione
    const page = parseInt(req.query.page) || 1;
    const limit = 3;
    const offset = (page - 1) * limit;

    // PRODUCTION-GRADE: Check cache first for better performance
    let groupList = groupsCache.get('all-groups');

    if (!groupList) {
      // Cache miss - fetch from WhatsApp (async, non-blocking)
      const groups = await sock.groupFetchAllParticipating();
      groupList = Object.values(groups).sort((a, b) => {
        const sa = (a?.subject || '').toLowerCase(), sb = (b?.subject || '').toLowerCase();
        return sa < sb ? 1 : sa > sb ? -1 : 0;
      });
      // Cache the result
      groupsCache.set('all-groups', groupList);
    }

    // Calcoli per la paginazione
    const totalGroups = groupList.length;
    const totalPages = Math.max(1, Math.ceil(totalGroups / limit));
    const paginatedGroups = groupList.slice(offset, offset + limit);

    // Escape WML sicuro
    // Uses global escWml — single-pass O(L) instead of O(5L)

    // Lista gruppi
    const list =
      paginatedGroups
        .map((g, idx) => {
          const globalIdx = offset + idx;
          const memberCount = g?.participants?.length || 0;
          return `<p><b>${globalIdx + 1}.</b> ${escWml(
            g.subject || t('groups.title')
          )}<br/>
        <small>${memberCount} ${t('groups.members')} | ${escWml(
            g.id.slice(-8)
          )}...</small><br/>
        <a href="/wml/group.view.wml?gid=${encodeURIComponent(
          g.id
        )}" accesskey="${Math.min(idx + 1, 9)}">[${Math.min(
            idx + 1,
            9
          )}] ${t('groups.open')}</a> |
        <a href="/wml/chat.wml?jid=${encodeURIComponent(
          g.id
        )}&amp;limit=3">${t('groups.chat')}</a>
      </p>`;
        })
        .join("") || `<p>No groups found.</p>`;

    // Controlli paginazione
    let paginationControls = "";
    if (totalPages > 1) {
      paginationControls = `<p><b>${t('common.pages')}</b><br/>`;

      if (page > 1) {
        paginationControls += `<a href="/wml/groups.wml?page=1">[First]</a> `;
        paginationControls += `<a href="/wml/groups.wml?page=${
          page - 1
        }">[&lt;]</a> `;
      }

      const startPage = Math.max(1, page - 2);
      const endPage = Math.min(totalPages, page + 2);

      for (let i = startPage; i <= endPage; i++) {
        if (i === page) {
          paginationControls += `<b>[${i}]</b> `;
        } else {
          paginationControls += `<a href="/wml/groups.wml?page=${i}">[${i}]</a> `;
        }
      }

      if (page < totalPages) {
        paginationControls += `<a href="/wml/groups.wml?page=${
          page + 1
        }">[&gt;]</a> `;
        paginationControls += `<a href="/wml/groups.wml?page=${totalPages}">[Last]</a>`;
      }

      paginationControls += `<br/><small>Page ${page} of ${totalPages} (${totalGroups} groups)</small></p>`;
    }

    // Form ricerca
    const searchForm = `
      <p><b>${t('groups.search')}</b></p>
      <p>
        <input name="q" title="${t('groups.search_placeholder')}" value="" emptyok="true" size="15" maxlength="30"/>
      </p>
      <p>
        <anchor title="${t('groups.search_btn')}">${t('groups.search_btn')}
          <go href="/wml/groups.search.wml" method="get">
            <postfield name="q" value="$(q)"/>
          </go>
        </anchor>
      </p>
      <do type="accept" label="${t('groups.search_btn')}">
        <go href="/wml/groups.search.wml" method="get">
          <postfield name="q" value="$(q)"/>
        </go>
      </do>`;

    // Body card
    const body = `
      <p><b>${t('groups.title')} (${totalGroups}) - ${t('common.page')} ${page}/${totalPages || 1}</b></p>
      ${searchForm}
      ${list}
      ${paginationControls}
      <p><b>Group Actions:</b></p>
      <p>
        <a href="/wml/group.create.wml" accesskey="*">${t('groups.create')}</a>
      </p>
      <p>
        <a href="/wml/home.wml">${t('groups.home')}</a>
        <a href="/wml/chats.wml">${t('groups.chats')}</a>
        <a href="/wml/contacts.wml">${t('groups.contacts')}</a>
      </p>
      <do type="accept" label="${t('group_create.create')}">
        <go href="/wml/group.create.wml"/>
      </do>
      <do type="options" label="${t('common.menu')}">
        <go href="/wml/menu.wml"/>
      </do>`;

    const wmlOutput = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
  <head>
    <meta http-equiv="Cache-Control" content="no-cache, no-store"/>
  </head>
  <card id="groups" title="${t('groups.title')}">
    ${body}
  </card>
</wml>`;

    sendRawWmlAware(res, wmlOutput);
  } catch (e) {
    const errorWml = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
  <card id="error" title="Error">
    <p><b>Error:</b></p>
    <p>${e.message || "Failed to load groups"}</p>
    <p><a href="/wml/home.wml">[Back to Home]</a></p>
  </card>
</wml>`;

    sendRawWmlAware(res, errorWml);
  }
});

// Group View - View group details, participants, settings (PRODUCTION-GRADE)
// Update group metadata handling
app.get("/wml/group.view.wml", async (req, res) => {
  try {
    if (!sock) throw new Error("Not connected");

    const gid = req.query.gid || "";
    if (!gid) throw new Error("No group ID provided");

    // Fetch group metadata - now returns LID-based information
    const metadata = await sock.groupMetadata(gid);

    // Extract group info with LID support
    const groupName = metadata.subject || "Unnamed Group";
    const groupDesc = metadata.desc || "No description";
    const participants = metadata.participants || [];
    // O(N) single-pass instead of O(2N) filter+map
    const adminSet = new Set();
    for (const p of participants) { if (p.admin) adminSet.add(p.id); }
    const isAdmin = adminSet.has(sock.user?.id);
    
    // Handle owner fields
    const owner = metadata.owner; // Now LID
    const ownerPn = metadata.ownerPn; // Phone number if available
    const createdAt = metadata.creation ? new Date(metadata.creation * 1000).toLocaleDateString() : "Unknown";

    // WML escape
    const esc = (text) =>
      (text || "")
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/"/g, "&quot;")
        .replace(/'/g, "&apos;");

    // Pagination for participants
    const page = parseInt(req.query.page) || 1;
    const limit = 3; // 3 partecipanti per pagina
    const offset = (page - 1) * limit;
    const totalPages = Math.ceil(participants.length / limit);
    const paginatedParticipants = participants.slice(offset, offset + limit);

    // Participant list with LID support
    const participantList = paginatedParticipants
      .map((p, idx) => {
        const globalIdx = offset + idx;
        // Handle participant ID (could be LID or PN)
        const participantId = p.id;
        const isLid = participantId.startsWith('lid:');
        const displayName = isLid ? 
          `LID:${participantId.substring(4)}` : 
          jidFriendly(participantId);
        const role = p.admin ? " (Admin)" : "";
        return `<p>${globalIdx + 1}. ${esc(displayName)}${role}</p>`;
      })
      .join("");

    // Pagination navigation
    const prevLink = page > 1
      ? `<a href="/wml/group.view.wml?gid=${encodeURIComponent(gid)}&amp;page=${page - 1}" accesskey="7">[7] Prev</a> `
      : "";
    const nextLink = page < totalPages
      ? `<a href="/wml/group.view.wml?gid=${encodeURIComponent(gid)}&amp;page=${page + 1}" accesskey="8">[8] Next</a>`
      : "";
    const pagination = (prevLink || nextLink)
      ? `<p>${prevLink}${nextLink} (${page}/${totalPages})</p>`
      : "";

    const ownerDisplay = ownerPn ? jidFriendly(ownerPn) : (owner ? jidFriendly(owner) : "Unknown");

    const body = `
      <p><b>${esc(groupName)}</b></p>
      <p><small>Created: ${esc(createdAt)} by ${esc(ownerDisplay)}</small></p>
      <p>${esc(groupDesc)}</p>
      <p><b>Members (${participants.length}):</b></p>
      ${participantList}
      ${pagination}
      <p>
        <a href="/wml/chat.wml?jid=${encodeURIComponent(gid)}&amp;limit=3" accesskey="1">[1] Open Chat</a><br/>
        ${isAdmin ? `<a href="/wml/group.edit.wml?gid=${encodeURIComponent(gid)}" accesskey="2">[2] Edit Group</a><br/>` : ""}
        <a href="/wml/group.invite.wml?gid=${encodeURIComponent(gid)}" accesskey="3">[3] Invite Link</a><br/>
        <a href="/wml/group.leave.wml?gid=${encodeURIComponent(gid)}" accesskey="4">[4] Leave</a><br/>
        <a href="/wml/groups.wml" accesskey="0">[0] Back</a>
      </p>
    `;

    sendWml(res, card("group-view", esc(groupName), body));
  } catch (e) {
    const errorWml = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
  <card id="error" title="Error">
    <p><b>Error:</b></p>
    <p>${esc(e.message || "Failed to load group")}</p>
    <p><a href="/wml/groups.wml">[Back to Groups]</a></p>
  </card>
</wml>`;
    sendRawWmlAware(res, errorWml);
  }
});

// Group Create - Create new group (PRODUCTION-GRADE, NON-BLOCKING)
app.get("/wml/group.create.wml", (req, res) => {
  const body = `
    <p><b>Create New Group</b></p>

    <p>Enter group name:</p>
    <p>
      <input name="groupname" title="Group Name" value="" emptyok="false" size="20" maxlength="50"/>
    </p>

    <p>Add participants (phone numbers, one per line, without +):</p>
    <p>
      <input name="participants" title="Participants" value="" emptyok="true" size="20" maxlength="200"/>
    </p>

    <p><small>Example: 393331234567</small></p>

    <p>
      <anchor title="Create">Create
        <go href="/wml/group.create.action.wml" method="post">
          <postfield name="groupname" value="$(groupname)"/>
          <postfield name="participants" value="$(participants)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.create')}">
      <go href="/wml/group.create.action.wml" method="post">
        <postfield name="groupname" value="$(groupname)"/>
        <postfield name="participants" value="$(participants)"/>
      </go>
    </do>

    <p>
      <a href="/wml/groups.wml" accesskey="0">[0] Cancel</a>
    </p>
  `;

  sendWml(res, card("group-create", "Create Group", body));
});

// Group Create Action - Process group creation (NON-BLOCKING)
app.post("/wml/group.create.action.wml", async (req, res) => {
  try {
    if (!sock) throw new Error("Not connected");

    const groupName = (req.body.groupname || "").trim();
    const participantsStr = (req.body.participants || "").trim();

    if (!groupName) throw new Error("Group name is required");
    if (!participantsStr) throw new Error("At least one participant is required");

    // Parse participants - non-blocking
    const participantNumbers = participantsStr
      .split(/[\n,;]+/)
      .map(p => p.trim())
      .filter(p => p.length > 0)
      .map(p => formatJid(p));

    if (participantNumbers.length === 0) {
      throw new Error("No valid participants provided");
    }

    // Create group - async operation
    const group = await sock.groupCreate(groupName, participantNumbers);

    // Invalidate groups cache since we created a new group
    groupsCache.invalidate('all-groups');

    const body = `
      <p><b>Group Created!</b></p>
      <p>Name: ${esc(groupName)}</p>
      <p>Members: ${participantNumbers.length}</p>
      <p>ID: ${esc(group.id.slice(-12))}...</p>

      <p>
        <a href="/wml/group.view.wml?gid=${encodeURIComponent(group.id)}" accesskey="1">[1] View Group</a><br/>
        <a href="/wml/chat.wml?jid=${encodeURIComponent(group.id)}&amp;limit=3" accesskey="2">[2] Open Chat</a><br/>
        <a href="/wml/groups.wml" accesskey="0">[0] All Groups</a>
      </p>
    `;

    sendWml(res, card("group-created", "Success", body));
  } catch (e) {
    const body = `
      <p><b>Error Creating Group</b></p>
      <p>${esc(e.message || "Failed to create group")}</p>
      <p>
        <a href="/wml/group.create.wml">[Try Again]</a><br/>
        <a href="/wml/groups.wml">[Back to Groups]</a>
      </p>
    `;
    sendWml(res, card("error", "Error", body));
  }
});

// Group Leave - Leave group (NON-BLOCKING)
app.get("/wml/group.leave.wml", async (req, res) => {
  try {
    const gid = req.query.gid || "";
    if (!gid) throw new Error("No group ID provided");

    const confirmed = req.query.confirm === "yes";

    if (!confirmed) {
      // Show confirmation page
      const metadata = await sock.groupMetadata(gid);
      const groupName = metadata.subject || "Unnamed Group";

      const body = `
        <p><b>Leave Group?</b></p>
        <p>Are you sure you want to leave:</p>
        <p><b>${esc(groupName)}</b></p>

        <p>
          <a href="/wml/group.leave.wml?gid=${encodeURIComponent(gid)}&amp;confirm=yes" accesskey="1">[1] Yes, Leave</a><br/>
          <a href="/wml/group.view.wml?gid=${encodeURIComponent(gid)}" accesskey="0">[0] Cancel</a>
        </p>
      `;

      sendWml(res, card("leave-confirm", "Confirm", body));
    } else {
      // Execute leave - non-blocking
      await sock.groupLeave(gid);

      // Invalidate groups cache since we left a group
      groupsCache.invalidate('all-groups');

      const body = `
        <p><b>Left Group</b></p>
        <p>You have left the group successfully.</p>
        <p>
          <a href="/wml/groups.wml" accesskey="1">[1] All Groups</a><br/>
          <a href="/wml/home.wml" accesskey="0">[0] Home</a>
        </p>
      `;

      sendWml(res, card("left", "Success", body));
    }
  } catch (e) {
    const body = `
      <p><b>Error</b></p>
      <p>${esc(e.message || "Failed to leave group")}</p>
      <p><a href="/wml/groups.wml">[Back to Groups]</a></p>
    `;
    sendWml(res, card("error", "Error", body));
  }
});

// =================== GROUP MANAGEMENT WML ROUTES ===================

app.get("/wml/group.edit.wml", async (req, res) => {
  const gid = req.query.gid || "";
  try {
    if (!sock) throw new Error("Not connected");
    if (!gid) throw new Error("No group ID provided");
    const metadata = await sock.groupMetadata(gid);
    const groupName = metadata.subject || "";
    const groupDesc = metadata.desc || "";
    const body = `
      <p><b>Edit Group</b></p>
      <p>Name:</p>
      <input name="name" title="Group name" value="${esc(groupName)}" size="25" maxlength="100"/>
      <p>Description:</p>
      <input name="desc" title="Description" value="${esc(groupDesc)}" size="25" maxlength="512"/>
      <p>
        <anchor title="Save">Save
          <go method="post" href="/wml/group.edit">
            <postfield name="gid" value="${esc(gid)}"/>
            <postfield name="name" value="$(name)"/>
            <postfield name="desc" value="$(desc)"/>
          </go>
        </anchor>
      </p>
      <do type="accept" label="${t('common.save')}">
        <go method="post" href="/wml/group.edit">
          <postfield name="gid" value="${esc(gid)}"/>
          <postfield name="name" value="$(name)"/>
          <postfield name="desc" value="$(desc)"/>
        </go>
      </do>
      <p><a href="/wml/group.view.wml?gid=${encodeURIComponent(gid)}" accesskey="0">[0] Cancel</a></p>
    `;
    sendWml(res, card("group-edit", "Edit Group", body));
  } catch (e) {
    sendWml(res, resultCard("Error", [e.message || "Failed to load group"], `/wml/group.view.wml?gid=${encodeURIComponent(gid)}`));
  }
});

app.post("/wml/group.edit", async (req, res) => {
  const { gid, name, desc } = req.body;
  try {
    if (!sock) throw new Error("Not connected");
    const trimmedName = (name || "").trim();
    const trimmedDesc = (desc || "").trim();
    if (trimmedName) await sock.groupUpdateSubject(gid, trimmedName);
    if (trimmedDesc !== undefined) await sock.groupUpdateDescription(gid, trimmedDesc);
    sendWml(res, resultCard("Saved", ["Group updated successfully"], `/wml/group.view.wml?gid=${encodeURIComponent(gid)}`));
  } catch (e) {
    sendWml(res, resultCard("Error", [e.message || "Update failed"], `/wml/group.edit.wml?gid=${encodeURIComponent(gid)}`));
  }
});

app.get("/wml/group.invite.wml", async (req, res) => {
  const gid = req.query.gid || "";
  try {
    if (!sock) throw new Error("Not connected");
    if (!gid) throw new Error("No group ID provided");
    const code = await sock.groupInviteCode(gid);
    const inviteLink = `https://chat.whatsapp.com/${code}`;
    const body = `
      <p><b>Group Invite Link</b></p>
      <p><small>${esc(inviteLink)}</small></p>
      <p><small>Share this link to invite people to the group.</small></p>
      <p><a href="/wml/group.view.wml?gid=${encodeURIComponent(gid)}" accesskey="0">[0] Back</a></p>
      <do type="accept" label="${t('common.refresh')}">
        <go href="/wml/group.invite.wml?gid=${encodeURIComponent(gid)}"/>
      </do>
    `;
    sendWml(res, card("group-invite", "Invite Link", body));
  } catch (e) {
    sendWml(res, resultCard("Error", [e.message || "Failed to get invite link"], `/wml/group.view.wml?gid=${encodeURIComponent(gid)}`));
  }
});

// Status Broadcast - Main page for posting status updates (PRODUCTION-GRADE)
app.get("/wml/status-broadcast.wml", (req, res) => {
  const body = `
    <p><b>${t('status_broadcast.title')}</b></p>
    <p>${t('status_broadcast.description')}</p>

    <p><b>${t('status_broadcast.select_type')}</b></p>
    <p>
      <a href="/wml/status.text.wml" accesskey="1">${t('status_broadcast.text_status')}</a><br/>
      <a href="/wml/status.image.wml" accesskey="2">${t('status_broadcast.image_status')}</a><br/>
      <a href="/wml/status.video.wml" accesskey="3">${t('status_broadcast.video_status')}</a>
    </p>

    <p><b>${t('status_broadcast.info')}</b></p>
    <p><small>${t('status_broadcast.info_text')}</small></p>

    <p>
      <a href="/wml/home.wml" accesskey="0">${t('status_broadcast.home')}</a> |
      <a href="/wml/menu.wml">[Menu]</a>
    </p>

    <do type="accept" label="${t('status_broadcast.text_status')}">
      <go href="/wml/status.text.wml"/>
    </do>
  `;

  sendWml(res, card("status-broadcast", t('status_broadcast.title'), body));
});

// Status Text - Post text status (FAST, NON-BLOCKING)
app.get("/wml/status.text.wml", (req, res) => {
  const body = `
    <p><b>Post Text Status</b></p>

    <p>Enter your status message:</p>
    <p>
      <input name="text" title="Status Text" value="" emptyok="false" size="25" maxlength="700"/>
    </p>

    <p><small>Max 700 characters. Visible for 24 hours.</small></p>

    <p>
      <anchor title="Post">Post
        <go href="/wml/status.text.action.wml" method="post">
          <postfield name="text" value="$(text)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.post')}">
      <go href="/wml/status.text.action.wml" method="post">
        <postfield name="text" value="$(text)"/>
      </go>
    </do>

    <p>
      <a href="/wml/status-broadcast.wml" accesskey="0">[0] Back</a>
    </p>
  `;

  sendWml(res, card("status-text", "Text Status", body));
});

// Status Text Action - Post text status (NON-BLOCKING, PRODUCTION-GRADE)
app.post("/wml/status.text.action.wml", async (req, res) => {
  try {
    if (!sock) throw new Error("Not connected");

    const text = (req.body.text || "").trim();
    if (!text) throw new Error("Status text cannot be empty");

    // Post status - async, non-blocking
    const result = await sock.sendMessage("status@broadcast", { text });

    const body = `
      <p><b>${t('status_broadcast.posted')}</b></p>
      <p><small>${t('status_broadcast.broadcast_msg')}</small></p>

      <p><b>Preview:</b></p>
      <p>${esc(text.substring(0, 100))}${text.length > 100 ? "..." : ""}</p>

      <p><small>ID: ${result?.key?.id?.slice(-8) || "Unknown"}</small></p>

      <p>
        <a href="/wml/status-broadcast.wml" accesskey="1">[1] Post Another</a><br/>
        <a href="/wml/home.wml" accesskey="0">[0] Home</a>
      </p>
    `;

    sendWml(res, card("status-posted", "Success", body));
  } catch (e) {
    const body = `
      <p><b>Error Posting Status</b></p>
      <p>${esc(e.message || "Failed to post status")}</p>
      <p>
        <a href="/wml/status.text.wml">[Try Again]</a><br/>
        <a href="/wml/status-broadcast.wml">[Back]</a>
      </p>
    `;
    sendWml(res, card("error", "Error", body));
  }
});

// Status Image - Post image status (NON-BLOCKING)
app.get("/wml/status.image.wml", (req, res) => {
  const body = `
    <p><b>Post Image Status</b></p>

    <p>Enter image URL:</p>
    <p>
      <input name="url" title="Image URL" value="" emptyok="false" size="30" maxlength="500"/>
    </p>

    <p>Optional caption:</p>
    <p>
      <input name="caption" title="Caption" value="" emptyok="true" size="25" maxlength="200"/>
    </p>

    <p><small>Image will be visible for 24 hours.</small></p>

    <p>
      <anchor title="Post">Post
        <go href="/wml/status.image.action.wml" method="post">
          <postfield name="url" value="$(url)"/>
          <postfield name="caption" value="$(caption)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.post')}">
      <go href="/wml/status.image.action.wml" method="post">
        <postfield name="url" value="$(url)"/>
        <postfield name="caption" value="$(caption)"/>
      </go>
    </do>

    <p>
      <a href="/wml/status-broadcast.wml" accesskey="0">[0] Back</a>
    </p>
  `;

  sendWml(res, card("status-image", "Image Status", body));
});

// Status Image Action - Post image status (NON-BLOCKING, PRODUCTION-GRADE)
app.post("/wml/status.image.action.wml", async (req, res) => {
  try {
    if (!sock) throw new Error("Not connected");

    const url = (req.body.url || "").trim();
    const caption = (req.body.caption || "").trim();

    if (!url) throw new Error("Image URL is required");

    // Download image - async, non-blocking
    const response = await axios.get(url, {
      responseType: "arraybuffer",
      timeout: 30000,
    });

    const imageBuffer = Buffer.from(response.data);

    // Post status with image - async
    const messageOptions = { image: imageBuffer };
    if (caption) messageOptions.caption = caption;

    const result = await sock.sendMessage("status@broadcast", messageOptions);

    const body = `
      <p><b>${t('status_broadcast.image_posted')}</b></p>
      <p><small>${t('status_broadcast.broadcast_msg')}</small></p>

      ${caption ? `<p><b>Caption:</b> ${esc(caption)}</p>` : ""}

      <p><small>ID: ${result?.key?.id?.slice(-8) || "Unknown"}</small></p>

      <p>
        <a href="/wml/status-broadcast.wml" accesskey="1">[1] Post Another</a><br/>
        <a href="/wml/home.wml" accesskey="0">[0] Home</a>
      </p>
    `;

    sendWml(res, card("status-posted", "Success", body));
  } catch (e) {
    const body = `
      <p><b>Error Posting Image Status</b></p>
      <p>${esc(e.message || t('status_broadcast.post_failed'))}</p>
      <p>
        <a href="/wml/status.image.wml">[Try Again]</a><br/>
        <a href="/wml/status-broadcast.wml">[Back]</a>
      </p>
    `;
    sendWml(res, card("error", "Error", body));
  }
});

// Status Video - Post video status (NON-BLOCKING)
app.get("/wml/status.video.wml", (req, res) => {
  const body = `
    <p><b>Post Video Status</b></p>

    <p>Enter video URL:</p>
    <p>
      <input name="url" title="Video URL" value="" emptyok="false" size="30" maxlength="500"/>
    </p>

    <p>Optional caption:</p>
    <p>
      <input name="caption" title="Caption" value="" emptyok="true" size="25" maxlength="200"/>
    </p>

    <p><small>Video will be visible for 24 hours.</small></p>

    <p>
      <anchor title="Post">Post
        <go href="/wml/status.video.action.wml" method="post">
          <postfield name="url" value="$(url)"/>
          <postfield name="caption" value="$(caption)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.post')}">
      <go href="/wml/status.video.action.wml" method="post">
        <postfield name="url" value="$(url)"/>
        <postfield name="caption" value="$(caption)"/>
      </go>
    </do>

    <p>
      <a href="/wml/status-broadcast.wml" accesskey="0">[0] Back</a>
    </p>
  `;

  sendWml(res, card("status-video", "Video Status", body));
});

// Status Video Action - Post video status (NON-BLOCKING, PRODUCTION-GRADE)
app.post("/wml/status.video.action.wml", async (req, res) => {
  try {
    if (!sock) throw new Error("Not connected");

    const url = (req.body.url || "").trim();
    const caption = (req.body.caption || "").trim();

    if (!url) throw new Error("Video URL is required");

    // Download video - async, non-blocking
    const response = await axios.get(url, {
      responseType: "arraybuffer",
      timeout: 60000, // 60 seconds for larger videos
    });

    const videoBuffer = Buffer.from(response.data);

    // Post status with video - async
    const messageOptions = { video: videoBuffer };
    if (caption) messageOptions.caption = caption;

    const result = await sock.sendMessage("status@broadcast", messageOptions);

    const body = `
      <p><b>${t('status_broadcast.video_posted')}</b></p>
      <p><small>${t('status_broadcast.broadcast_msg')}</small></p>

      ${caption ? `<p><b>Caption:</b> ${esc(caption)}</p>` : ""}

      <p><small>ID: ${result?.key?.id?.slice(-8) || "Unknown"}</small></p>

      <p>
        <a href="/wml/status-broadcast.wml" accesskey="1">[1] Post Another</a><br/>
        <a href="/wml/home.wml" accesskey="0">[0] Home</a>
      </p>
    `;

    sendWml(res, card("status-posted", "Success", body));
  } catch (e) {
    const body = `
      <p><b>Error Posting Video Status</b></p>
      <p>${esc(e.message || t('status_broadcast.post_failed'))}</p>
      <p>
        <a href="/wml/status.video.wml">[Try Again]</a><br/>
        <a href="/wml/status-broadcast.wml">[Back]</a>
      </p>
    `;
    sendWml(res, card("error", "Error", body));
  }
});

app.get("/wml/search.results.wml", (req, res) => {
  const q = String(req.query.q || "").trim();
  const searchType = req.query.type || "messages";
  const limitParam = req.query.limit || "10";
  const limit =
    limitParam === "all"
      ? Infinity
      : Math.max(1, Math.min(50, parseInt(limitParam)));
  const page = Math.max(1, parseInt(req.query.page || "1"));
  const pageSize = 3;
  if (!q || q.length < 2) {
    sendWml(
      res,
      resultCard(
        "Search Error",
        ["Query must be at least 2 characters"],
        "/wml/home.wml"
      )
    );
    return;
  }
  let allResults = [];
  const searchLower = q.toLowerCase();
  // funzione sicura per troncare
  function truncate(str, n) {
    return str && str.length > n ? str.slice(0, n) + "..." : str;
  }
  // Funzione per formattare il timestamp
  function formatTimestamp(timestamp) {
    if (!timestamp || timestamp === 0) return "Unknown";
    return new Date(Number(timestamp) * 1000).toLocaleString("en-GB", {
      day: "2-digit",
      month: "short",
      year: "numeric",
      hour: "2-digit",
      minute: "2-digit",
      second: "2-digit",
    });
  }
  const descByTimestamp = (a, b) => b.timestamp - a.timestamp;
  const effectiveLimit = limit === Infinity ? Infinity : limit;

  if (searchType === "messages") {
    // O(C*M) worst-case full scan, but early-breaks at `effectiveLimit` results
    // Per-message check is O(L) where L = message text length (uses cached lowercase text)
    for (const [chatId, messages] of chatStore.entries()) {
      const contact = contactStore.get(chatId);
      const chatName = contact?.name || contact?.notify || jidFriendly(chatId);

      for (const msg of messages) {
        const cachedText = getMessageSearchText(msg);
        if (!cachedText.includes(searchLower)) continue;

        const content = extractMessageContent(msg.message);
        let text = '', messageType = '';
        if (content?.conversation) { text = content.conversation; messageType = 'text'; }
        else if (content?.extendedTextMessage?.text) { text = content.extendedTextMessage.text; messageType = 'text'; }
        else if (content?.imageMessage) { text = '[Image] ' + (content.imageMessage.caption || ''); messageType = 'image'; }
        else if (content?.videoMessage) { text = '[Video] ' + (content.videoMessage.caption || ''); messageType = 'video'; }
        else if (content?.audioMessage) { text = `[Audio ${content.audioMessage.seconds || 0}s]`; messageType = 'audio'; if (msg.transcription && msg.transcription !== '[Trascrizione fallita]' && msg.transcription !== '[Audio troppo lungo per la trascrizione]') text += ' ' + msg.transcription; }
        else if (content?.documentMessage) { text = '[Document] ' + (content.documentMessage.fileName || ''); messageType = 'document'; }
        else if (content?.stickerMessage) { text = '[Sticker]'; messageType = 'sticker'; }
        else if (content?.locationMessage) { text = '[Location]'; messageType = 'location'; }
        else if (content?.contactMessage) { text = '[Contact]'; messageType = 'contact'; }

        const timestamp = Number(msg.messageTimestamp) || 0;
        allResults.push({
          type: 'message', chatId, chatName, messageId: msg.key.id,
          text: truncate(text, 40), timestamp,
          formattedTime: formatTimestamp(timestamp),
          fromMe: msg.key.fromMe, messageType,
          audioInfo: messageType === 'audio' ? {
            duration: content?.audioMessage?.seconds || 0,
            hasTranscription: !!(msg.transcription && msg.transcription !== '[Trascrizione fallita]' && msg.transcription !== '[Audio troppo lungo per la trascrizione]'),
          } : null,
        });

        if (effectiveLimit !== Infinity && allResults.length >= effectiveLimit) break;
      }
      if (effectiveLimit !== Infinity && allResults.length >= effectiveLimit) break;
    }
    trimSearchTextCache();
    // Top-K sort: only sort what we need for pagination instead of full O(R log R)
    const needed = Math.min(allResults.length, (page) * pageSize);
    allResults = needed < allResults.length ? topK(allResults, needed, descByTimestamp) : allResults.sort(descByTimestamp);
  } else if (searchType === "contacts") {
    // Iterate Map directly instead of Array.from() allocation + filter
    for (const c of contactStore.values()) {
      const name = (c.name || c.notify || c.verifiedName || '').toLowerCase();
      const number = c.id.replace('@s.whatsapp.net', '');
      if (!name.includes(searchLower) && !number.includes(searchLower)) continue;

      const msgs = chatStore.get(c.id) || [];
      const lastMessage = msgs.length > 0 ? msgs[msgs.length - 1] : null;
      const timestamp = lastMessage ? Number(lastMessage.messageTimestamp) : 0;

      allResults.push({
        type: 'contact',
        name: c.name || c.notify || c.verifiedName || 'Unknown',
        number: jidFriendly(c.id), jid: c.id,
        timestamp, formattedTime: formatTimestamp(timestamp),
        lastMessageText: lastMessage ? truncate(messageText(lastMessage), 30) : 'No messages',
      });

      if (effectiveLimit !== Infinity && allResults.length >= effectiveLimit) break;
    }
    const needed = Math.min(allResults.length, (page) * pageSize);
    allResults = needed < allResults.length ? topK(allResults, needed, descByTimestamp) : allResults.sort(descByTimestamp);
  } else if (searchType === "chats") {
    for (const [chatId, messages] of chatStore.entries()) {
      const contact = contactStore.get(chatId);
      const isGroup = chatId.endsWith('@g.us');
      const chatName = isGroup
        ? contact?.subject || contact?.name || 'Unnamed Group'
        : contact?.name || contact?.notify || contact?.verifiedName || jidFriendly(chatId);

      // Pre-lowercased comparison
      if (!chatName.toLowerCase().includes(searchLower)) continue;

      const lastMessage = messages.length > 0 ? messages[messages.length - 1] : null;
      const timestamp = lastMessage ? Number(lastMessage.messageTimestamp) : 0;

      allResults.push({
        type: 'chat', chatId, chatName, isGroup,
        messageCount: messages.length, timestamp,
        formattedTime: formatTimestamp(timestamp),
        phoneNumber: isGroup ? null : chatId.replace('@s.whatsapp.net', ''),
      });

      if (effectiveLimit !== Infinity && allResults.length >= effectiveLimit) break;
    }
    const needed = Math.min(allResults.length, (page) * pageSize);
    allResults = needed < allResults.length ? topK(allResults, needed, descByTimestamp) : allResults.sort(descByTimestamp);
  } else if (searchType === "groups") {
    for (const [chatId, messages] of chatStore.entries()) {
      if (!chatId.endsWith('@g.us')) continue;
      const contact = contactStore.get(chatId);
      const groupName = contact?.subject || contact?.name || 'Unnamed Group';

      if (!groupName.toLowerCase().includes(searchLower)) continue;

      const lastMessage = messages.length > 0 ? messages[messages.length - 1] : null;
      const timestamp = lastMessage ? Number(lastMessage.messageTimestamp) : 0;
      const memberCount = contact?.participants ? contact.participants.length : 0;

      allResults.push({
        type: 'group', chatId, chatName: groupName,
        messageCount: messages.length, timestamp,
        formattedTime: formatTimestamp(timestamp), memberCount,
      });

      if (effectiveLimit !== Infinity && allResults.length >= effectiveLimit) break;
    }
    const needed = Math.min(allResults.length, (page) * pageSize);
    allResults = needed < allResults.length ? topK(allResults, needed, descByTimestamp) : allResults.sort(descByTimestamp);
  }

  // pagination
  const totalResults = allResults.length;
  const totalPages = Math.ceil(totalResults / pageSize) || 1;
  const startIndex = (page - 1) * pageSize;
  const endIndex = Math.min(startIndex + pageSize, totalResults);
  const paginatedResults = allResults.slice(startIndex, endIndex);

  const resultList =
    paginatedResults
      .map((r, idx) => {
        const globalIndex = startIndex + idx + 1;
        if (r.type === "message") {
          let messagePrefix = "";
          if (r.messageType === "audio") {
            messagePrefix = "[AUDIO] ";
            if (r.audioInfo?.hasTranscription) {
              messagePrefix += "[TRANSCRIPTION] ";
            }
          } else if (r.messageType === "image") {
            messagePrefix = "[IMG] ";
          } else if (r.messageType === "video") {
            messagePrefix = "[VID] ";
          } else if (r.messageType === "document") {
            messagePrefix = "[DOC] ";
          } else if (r.messageType === "sticker") {
            messagePrefix = "[STICK] ";
          }

          return `<p><b>${globalIndex}.</b> ${messagePrefix}${esc(r.text)}<br/>
        <small>From: ${esc(r.chatName)} | ${r.formattedTime} | ${
            r.fromMe ? "Me" : "Them"
          }</small><br/>
        <a href="/wml/chat.wml?jid=${encodeURIComponent(
          r.chatId
        )}&amp;limit=3">[Open Chat]</a> 
        <a href="/wml/msg.wml?mid=${encodeURIComponent(
          r.messageId
        )}&amp;jid=${encodeURIComponent(r.chatId)}">[Message]</a>
        ${
          r.messageType === "audio" && r.audioInfo?.hasTranscription
            ? ` <a href="/wml/audio-transcription.wml?mid=${encodeURIComponent(
                r.messageId
              )}&amp;jid=${encodeURIComponent(r.chatId)}">[TRANSCRIPTION]</a>`
            : ""
        }
      </p>`;
        } else if (r.type === "contact") {
          return `<p><b>${globalIndex}.</b> ${esc(r.name)}<br/>
        <small>${esc(r.number)} | Last: ${r.formattedTime}</small><br/>
        <small>Last msg: ${esc(r.lastMessageText)}</small><br/>
        <a href="/wml/contact.wml?jid=${encodeURIComponent(r.jid)}">[View]</a> |
        <a href="/wml/chat.wml?jid=${encodeURIComponent(
          r.jid
        )}&amp;limit=3">[Chat]</a>
      </p>`;
        } else if (r.type === "chat") {
          const typeIcon = r.isGroup ? "[GROUP]" : "[CHAT]";
          const phoneInfo = r.phoneNumber ? ` | ${r.phoneNumber}` : "";
          return `<p><b>${globalIndex}.</b> ${typeIcon} ${esc(r.chatName)}<br/>
        <small>${r.messageCount} messages | Last: ${
            r.formattedTime
          }${phoneInfo}</small><br/>
        <a href="/wml/chat.wml?jid=${encodeURIComponent(
          r.chatId
        )}&amp;limit=3">[Open]</a> |
        <a href="/wml/send.text.wml?to=${encodeURIComponent(
          r.chatId
        )}">[Send]</a>
        ${
          r.phoneNumber
            ? ` | <a href="wtai://wp/mc;${r.phoneNumber}">[Call]</a>`
            : ""
        }
      </p>`;
        } else if (r.type === "group") {
          const memberInfo =
            r.memberCount > 0 ? ` | ${r.memberCount} members` : "";
          return `<p><b>${globalIndex}.</b> [GROUP] ${esc(r.chatName)}<br/>
        <small>${r.messageCount} messages | Last: ${
            r.formattedTime
          }${memberInfo}</small><br/>
        <a href="/wml/chat.wml?jid=${encodeURIComponent(
          r.chatId
        )}&amp;limit=3">[Open]</a> |
        <a href="/wml/send.text.wml?to=${encodeURIComponent(
          r.chatId
        )}">[Send]</a>
      </p>`;
        }
        return "";
      })
      .join("") || "<p>No results found.</p>";

  // pagination controls (come prima)
  let paginationControls = "";
  if (totalPages > 1) {
    paginationControls = `<p><b>${t('common.pages')}</b><br/>`;
    if (page > 1) {
      paginationControls += `<a href="/wml/search.results.wml?q=${encodeURIComponent(
        q
      )}&amp;type=${encodeURIComponent(
        searchType
      )}&amp;limit=${encodeURIComponent(
        limitParam
      )}&amp;page=1">[&lt;&lt; First]</a> `;
      paginationControls += `<a href="/wml/search.results.wml?q=${encodeURIComponent(
        q
      )}&amp;type=${encodeURIComponent(
        searchType
      )}&amp;limit=${encodeURIComponent(limitParam)}&amp;page=${
        page - 1
      }">[&lt; Prev]</a> `;
    }
    const startPage = Math.max(1, page - 2);
    const endPage = Math.min(totalPages, page + 2);
    if (startPage > 1) {
      paginationControls += `<a href="/wml/search.results.wml?q=${encodeURIComponent(
        q
      )}&amp;type=${encodeURIComponent(
        searchType
      )}&amp;limit=${encodeURIComponent(limitParam)}&amp;page=1">[1]</a> `;
      if (startPage > 2) paginationControls += "... ";
    }
    for (let i = startPage; i <= endPage; i++) {
      if (i === page) paginationControls += `<b>[${i}]</b> `;
      else
        paginationControls += `<a href="/wml/search.results.wml?q=${encodeURIComponent(
          q
        )}&amp;type=${encodeURIComponent(
          searchType
        )}&amp;limit=${encodeURIComponent(
          limitParam
        )}&amp;page=${i}">[${i}]</a> `;
    }
    if (endPage < totalPages) {
      if (endPage < totalPages - 1) paginationControls += "... ";
      paginationControls += `<a href="/wml/search.results.wml?q=${encodeURIComponent(
        q
      )}&amp;type=${encodeURIComponent(
        searchType
      )}&amp;limit=${encodeURIComponent(
        limitParam
      )}&amp;page=${totalPages}">[${totalPages}]</a> `;
    }
    if (page < totalPages) {
      paginationControls += `<a href="/wml/search.results.wml?q=${encodeURIComponent(
        q
      )}&amp;type=${encodeURIComponent(
        searchType
      )}&amp;limit=${encodeURIComponent(limitParam)}&amp;page=${
        page + 1
      }">[Next &gt;]</a> `;
      paginationControls += `<a href="/wml/search.results.wml?q=${encodeURIComponent(
        q
      )}&amp;type=${encodeURIComponent(
        searchType
      )}&amp;limit=${encodeURIComponent(
        limitParam
      )}&amp;page=${totalPages}">[Last &gt;&gt;]</a>`;
    }
    paginationControls += "</p>";
  }

  const limitDisplay = limitParam === "all" ? "No limit" : limitParam;
  const searchTypeDisplay =
    searchType.charAt(0).toUpperCase() + searchType.slice(1);
  const body = `
    <p><b>Search Results</b></p>
    <p>Query: <b>${esc(q)}</b></p>
    <p>Type: ${esc(searchTypeDisplay)} | Limit: ${limitDisplay}</p>
    <p>Page: ${page}/${totalPages} | Total: ${totalResults}</p>
    <p>Showing: ${startIndex + 1}-${endIndex} of ${totalResults}</p>
    <p><small>Sorted by most recent first</small></p>
    ${resultList}
    ${paginationControls}
    <p><b>Search Again:</b></p>
    <p>
      <a href="/wml/search.wml?q=${encodeURIComponent(
        q
      )}" accesskey="1">[1] New Search</a> |
      <a href="/wml/home.wml" accesskey="0">[0] Home</a>
    </p>
    <do type="accept" label="${t('home.title')}">
      <go href="/wml/home.wml"/>
    </do>
  `;
  sendWml(res, card("search-results", "Search Results", body));
});

// Enhanced Search Form
app.get("/wml/search.wml", (req, res) => {
  const prevQuery = esc(req.query.q || "");
  const prevLimit = req.query.limit || "5"; // default a 10

  const body = `
    <p><b>${t('search.title')}</b></p>

    <p>${t('search.search_for')}</p>
    <input name="q" title="${t('search.placeholder')}" value="${prevQuery}" size="20" maxlength="100"/>

    <p>${t('search.search_in')}</p>
    <select name="type" title="Search Type">
      <option value="messages">${t('search.messages')}</option>
      <option value="contacts">${t('search.contacts')}</option>
      <option value="chats">${t('search.chats')}</option>
      <option value="groups">${t('search.groups')}</option>
    </select>

    <p>${t('search.limit')}</p>
    <select name="limit" title="${t('search.max_results')}">
      <option value="5" ${
        prevLimit === "5" ? 'selected="selected"' : ""
      }>${t('search.results_5')}</option>
      <option value="10" ${
        prevLimit === "10" ? 'selected="selected"' : ""
      }>${t('search.results_10')}</option>
      <option value="20" ${
        prevLimit === "20" ? 'selected="selected"' : ""
      }>${t('search.results_20')}</option>
      <option value="50" ${
        prevLimit === "50" ? 'selected="selected"' : ""
      }>${t('search.results_50')}</option>
      <option value="all" ${
        prevLimit === "all" ? 'selected="selected"' : ""
      }>${t('search.no_limit')}</option>
    </select>

    <p>
      <anchor title="${t('search.search_btn')}">${t('search.search_btn')}
        <go href="/wml/search.results.wml" method="get">
          <postfield name="q" value="$(q)"/>
          <postfield name="type" value="$(type)"/>
          <postfield name="limit" value="$(limit)"/>
          <postfield name="chatJid" value="$(chatJid)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('search.search_btn')}">
      <go href="/wml/search.results.wml" method="get">
        <postfield name="q" value="$(q)"/>
        <postfield name="type" value="$(type)"/>
        <postfield name="limit" value="$(limit)"/>
        <postfield name="chatJid" value="$(chatJid)"/>
      </go>
    </do>

    ${navigationBar()}
  `;

  sendWml(res, card("search", t('search.title'), body));
});

// Auto-refresh for dynamic content
app.get("/wml/live-status.wml", (req, res) => {
  const refreshInterval = req.query.interval || "30";

  const body = `
   
    <p><b>Live Status Monitor</b></p>
    <p>Updates every ${refreshInterval} seconds</p>
    
    <p><b>Connection:</b> ${connectionState}</p>
    <p><b>Messages:</b> ${messageStore.size}</p>
    <p><b>Contacts:</b> ${contactStore.size}</p>
    <p><b>Chats:</b> ${chatStore.size}</p>
    <p><b>Time:</b> ${new Date().toLocaleTimeString()}</p>
    
  
    
    <p><a href="/wml/home.wml" accesskey="0">[0] Home</a></p>
    
   
  `;

  sendWml(
    res,
    card(
      "live-status",
      "Live Status",
      body,
      `/wml/live-status.wml?interval=${refreshInterval}`
    )
  );
});

// Add all the existing endpoints from your original code here...
// [Previous POST handlers for send.text, send.image, etc.]

// Keep all existing POST handlers and API endpoints
app.post("/wml/send.text", async (req, res) => {
  try {
    if (!sock) throw new Error("Not connected");
    const { to, message } = req.body;
    const result = await sock.sendMessage(formatJid(to), { text: message });
    sendWml(
      res,
      resultCard(
        "Message Sent",
        [
          `To: ${jidFriendly(to)}`,
          `Message: ${truncate(message, 50)}`,
          `ID: ${result?.key?.id || "Unknown"}`,
        ],
        `/wml/send-menu.wml?to=${encodeURIComponent(to)}`
      )
    );
  } catch (e) {
    sendWml(
      res,
      resultCard(
        "Send Failed",
        [e.message || "Failed to send"],
        "/wml/send.text.wml"
      )
    );
  }
});

// Chat history is now loaded from persistent storage only
// No need to fetch from WhatsApp servers - the initial sync handles everything
// Messages are saved in real-time via event handlers

async function performInitialSync() {
  try {
    if (!sock || connectionState !== "open") {
      logger.warn("Cannot sync: not connected");
      return;
    }

    logger.info(`Starting enhanced initial sync (attempt ${syncAttempts + 1})`);
    syncAttempts++;

    let successCount = 0;

    // Sync contacts
    try {
      logger.info("Checking contacts...");
      if (contactStore.size === 0) {
        logger.info("Waiting for contacts via events...");
        await delay(3000);
      }
      logger.info(`Contacts in store: ${contactStore.size}`);
      successCount++;
    } catch (err) {
      logger.error("Contact sync failed:", err.message);
    }

    // Sync chats
    try {
      logger.info("Fetching chats...");
      const groups = await sock.groupFetchAllParticipating();
      logger.info(`Retrieved ${Object.keys(groups).length} groups`);

      for (const chatId of Object.keys(groups)) {
        if (!chatStore.has(chatId)) {
          chatStore.set(chatId, []);
        }
      }

      if (chatStore.size === 0) {
        logger.info("Waiting for chats via events...");
        await delay(3000);
      }

      logger.info(`Chats in store: ${chatStore.size}`);
      successCount++;
    } catch (err) {
      logger.error("Chat sync failed:", err.message);
    }

    // Check sync completion
    const counts = {
      contacts: contactStore.size,
      chats: chatStore.size,
      messages: messageStore.size,
    };

    logger.info("Sync results:", counts);

    if (counts.contacts > 0 && counts.chats > 0) {
      isFullySynced = true;
      logger.info("Initial sync completed successfully!");
    } else if (syncAttempts < 15) {
      const delayMs = Math.min(syncAttempts * 5000, 60000);
      logger.info(`Sync incomplete, retrying in ${delayMs / 1000}s...`);
      setTimeout(performInitialSync, delayMs);
    } else {
      logger.warn("Sync attempts exhausted. Data may still load gradually.");
    }
  } catch (err) {
    logger.error("Initial sync failed:", err);
    if (syncAttempts < 15) {
      setTimeout(performInitialSync, 5000);
    }
  }
}

// Helper function for saving messages to DB
function saveMessageToDB(msg, jid) {
  if (!msg || !msg.key || !msg.key.id) return;

  try {
    // Save to message store
    messageStore.set(msg.key.id, msg);
    // Maintain reverse index
    messageToChatIndex.set(msg.key.id, jid);

    // Add to chat store if not exists
    if (!chatStore.has(jid)) {
      chatStore.set(jid, []);
    }
    if (!chatMessageIdSets.has(jid)) {
      chatMessageIdSets.set(jid, new Set());
    }

    const idSet = chatMessageIdSets.get(jid);
    // O(1) duplicate check instead of O(n) .some()
    if (!idSet.has(msg.key.id)) {
      idSet.add(msg.key.id);
      chatStore.get(jid).push(msg);
    }
  } catch (error) {
    logger.error('Error saving message to DB:', error.message);
  }
}

// ============ LOAD CHAT UTILS DEPENDENCIES ============
// Dependencies will be initialized after socket creation in connectWithBetterSync()
// This ensures sock is not null when passed to loadChatUtils

// Cache Baileys version to avoid network requests on every reconnect
let cachedBaileysVersion = null;

// Production-ready connection with better error handling
async function connectWithBetterSync() {
  // Prevent race conditions - only one connection attempt at a time
  if (isConnecting) {
    logger.warn('Connection already in progress, skipping duplicate attempt');
    return;
  }

  isConnecting = true;

  // Try to load saved QR code if available
  if (!currentQR) {
    const savedQR = loadQRFromFile();
    if (savedQR) {
      currentQR = savedQR;
      logger.info('QR code restored from file');
    }
  }

  try {
  const { state, saveCreds } = await useMultiFileAuthState("./auth_info_baileys", {
  signalKeys: {
    'lid-mapping': true,
    'device-list': true,
    'tctoken': true
  }
});
    // Use cached version to avoid network requests on every reconnect
    if (!cachedBaileysVersion) {
      const { version } = await fetchLatestBaileysVersion();
      cachedBaileysVersion = version;
      logger.info(`Baileys version fetched and cached: ${version}`);
    }

    const newSock = makeWASocket({
      version: cachedBaileysVersion,
      auth: state,
      printQRInTerminal: false,
      syncFullHistory: true,
      markOnlineOnConnect: false,
      emitOwnEvents: true,
      getMessage: async (key) => messageStore.get(key.id) || null,
      shouldIgnoreJid: (jid) => false,
      shouldSyncHistoryMessage: (msg) => true,
      browser: Browsers.macOS("Safari"),
      connectTimeoutMs: 300000,
      defaultQueryTimeoutMs: 300000,
      keepAliveIntervalMs: 25000,
      retryRequestDelayMs: 5000,
    });

    // Keep reference to old sock for cleanup, then assign new one
    const oldSock = sock;
    sock = newSock;

    // Initialize loadChatUtils dependencies NOW that sock is created
    initializeDependencies({
      logger: logger,
      sock: newSock,
      chatStore: chatStore,
      messageStore: messageStore,
      connectionState: connectionState,
      formatJid: formatJid,
      delay: delay,
      saveMessageToDB: saveMessageToDB,
      performInitialSync: performInitialSync
    });
    logger.info('✓ loadChatUtils dependencies initialized with active socket');

    // Check if already connected (when restarting with saved credentials)
    if (state?.creds?.registered) {
      connectionState = "connecting";
      logger.info("Detected existing credentials - setting state to 'connecting'");
    }

    if (process.env.WA_PHONE_NUMBER && !WA_PHONE_NUMBER) {
      logger.warn('WA_PHONE_NUMBER is set but invalid. Use digits only, with country code (example: 393401234567).');
    }

    

    newSock.ev.on("creds.update", saveCreds);

    // Guard: only this socket's events should trigger reconnection
    const currentSock = newSock;
    newSock.ev.on(
      "connection.update",
      async ({ connection, lastDisconnect, qr }) => {
        // Ignore events from stale sockets (old connection firing after new one started)
        if (sock !== currentSock) {
          logger.warn('Ignoring connection.update from stale socket');
          return;
        }

        // Update connection state
        if (connection) {
          connectionState = connection;
          logger.info(`Connection state updated: ${connectionState}`);
        }

        if (qr) {
          // If WA_PHONE_NUMBER is set, request a pairing code instead of showing QR
          if (WA_PHONE_NUMBER && !state?.creds?.registered) {
            try {
              const code = await newSock.requestPairingCode(WA_PHONE_NUMBER);
              currentPairingCode = code;
              currentQR = null; // no QR needed when using pairing code
              logger.info(`Pairing code generated: ${code} (for phone ${WA_PHONE_NUMBER})`);
            } catch (err) {
              logger.error(`Failed to request pairing code: ${err.message}`);
              // Fall back to QR
              currentQR = qr;
              currentPairingCode = null;
              saveQRToFile(qr);
            }
          } else {
            currentQR = qr;
            currentPairingCode = null;
            saveQRToFile(qr); // Save QR to file
            logger.info("QR Code generated and saved to file");
            if (isDev) {
              qrcode.generate(qr, { small: true });
            }
          }
        }

        if (connection === "close") {
          const statusCode = lastDisconnect?.error?.output?.statusCode;
          const errorMessage = lastDisconnect?.error?.message || 'Unknown error';

          // Reset connection flag so reconnection attempts are not blocked
          isConnecting = false;

          // Log detailed disconnect reason
          logger.warn(`Connection closed - Status: ${statusCode}, Error: ${errorMessage}`);

          // Only prevent reconnection on explicit logout
          const shouldReconnect = statusCode !== DisconnectReason.loggedOut;

          logger.info(`Should reconnect: ${shouldReconnect}`);

          if (shouldReconnect) {
            // Aggressive reconnection with minimal delay
            let delay = 2000; // Start with 2 seconds

            // Only use exponential backoff after many failed attempts
            if (syncAttempts > 5) {
              delay = Math.min(3000 * Math.pow(1.5, syncAttempts - 5), 15000);
            }

            logger.info(`Reconnecting in ${delay}ms (attempt ${syncAttempts + 1})...`);
            setTimeout(connectWithBetterSync, delay);
          } else {
            // Save data IMMEDIATELY before logout
            logger.info("Saving all data before logout...");
            (async () => {
              try {
                await storage.saveImmediately("contacts", contactStore);
                await storage.saveImmediately("chats", chatStore);
                await storage.saveImmediately("messages", messageStore);
                await storage.saveImmediately("meta", {
                  isFullySynced,
                  syncAttempts,
                  lastSync: new Date().toISOString(),
                  contactsCount: contactStore.size,
                  chatsCount: chatStore.size,
                  messagesCount: messageStore.size,
                });
                logger.info("✓ Data saved on logout");
              } catch (error) {
                logger.error("❌ Failed to save on logout:", error);
              }
            })();

            // DO NOT clear stores - keep data persistent
            // contactStore.clear();
            // chatStore.clear();
            // messageStore.clear();
            isFullySynced = false;
            syncAttempts = 0;
            clearQRFile(); // Clear QR file on logout
          }
        } else if (connection === "open") {
          logger.info("WhatsApp connected successfully!");
          isConnecting = false; // Connection established — allow future reconnections
          currentQR = null;
          currentPairingCode = null;
          clearQRFile(); // Clear QR file when connected

          // Only reset isFullySynced if we don't have data from disk
          // This prevents "syncing..." state when reconnecting with persistent data
          if (contactStore.size === 0 && chatStore.size === 0) {
            isFullySynced = false;
          } else {
            logger.info(`Keeping data from disk: ${contactStore.size} contacts, ${chatStore.size} chats`);
            // Mark as synced if we have data, will be updated by events
            isFullySynced = true;
          }

          syncAttempts = 0;

          // Start sync process to update with latest data
          setTimeout(enhancedInitialSync, 5000);
        }
      }
    );

    // Enhanced event handlers
    newSock.ev.on(
      "messaging-history.set",
      ({ chats, contacts, messages, isLatest }) => {
        logger.info(
          `History batch - Chats: ${chats.length}, Contacts: ${contacts.length}, Messages: ${messages.length}`
        );

        // Single-pass partition instead of 4x O(N) .filter()
        const [jidChats, lidChats] = partitionByLid(chats);
        for (const chat of [...jidChats, ...lidChats]) {
          if (!chatStore.has(chat.id)) {
            chatStore.set(chat.id, []);
          }
        }

        const [jidContacts, lidContacts] = partitionByLid(contacts);

        for (const contact of [...jidContacts, ...lidContacts]) {
          contactStore.set(contact.id, contact);
          // Maintain phone→contact index
          if (contact.phoneNumber) {
            phoneToContactIndex.set(contact.phoneNumber, contact.id);
          }
          const numericPart = contact.id.replace(/@.*$/, '');
          if (numericPart) {
            phoneToContactIndex.set(numericPart, contact.id);
          }
        }

        for (const msg of messages) {
          if (msg.key?.id) {
            messageStore.set(msg.key.id, msg);
            const chatId = msg.key.remoteJid;
            if (!chatStore.has(chatId)) {
              chatStore.set(chatId, []);
            }
            if (!chatMessageIdSets.has(chatId)) {
              chatMessageIdSets.set(chatId, new Set());
            }
            // Maintain indexes
            messageToChatIndex.set(msg.key.id, chatId);
            // Dedup: only push if not already in store
            if (!chatMessageIdSets.get(chatId).has(msg.key.id)) {
              chatMessageIdSets.get(chatId).add(msg.key.id);
              chatStore.get(chatId).push(msg);
            }
          }
        }

        // Save every batch to avoid data loss on crash during multi-batch sync
        saveMessages();
        saveChats();

        if (isLatest) {
          // Sort all chat message arrays by timestamp so getRecentChats() works correctly
          for (const msgs of chatStore.values()) {
            msgs.sort((a, b) => (Number(a.messageTimestamp) || 0) - (Number(b.messageTimestamp) || 0));
          }
          logger.info("Bulk history sync complete");
          isFullySynced = true;
          saveAll();
        }
      }
    );
    // Replace the messages.upsert event handler with this fixed version

 newSock.ev.on("messages.upsert", async ({ messages }) => {
  let newMessagesCount = 0;
  const MAX_MESSAGES_PER_CHAT = 1000;

  for (const message of messages) {
    if (message.key?.id) {
      // OPTIMIZATION: Check if message already exists (avoid duplicates)
      const existingMessage = messageStore.get(message.key.id);
      if (existingMessage) {
        continue; // Skip duplicates
      }

      newMessagesCount++;
      messageStore.set(message.key.id, message);

      // Handle LID/PN in message keys
      const chatId = message.key.remoteJidAlt || message.key.remoteJid;

      // Maintain cached unread counter — O(1) increment
      if (!message.key.fromMe && !message.messageStubType && message.message) {
        incrementUnreadCount(chatId);
      }
      const participant = message.key.participantAlt || message.key.participant;

      // Maintain reverse index
      messageToChatIndex.set(message.key.id, chatId);

      if (!chatStore.has(chatId)) {
        chatStore.set(chatId, []);
      }
      if (!chatMessageIdSets.has(chatId)) {
        chatMessageIdSets.set(chatId, new Set());
      }
      const chatMessages = chatStore.get(chatId);
      const idSet = chatMessageIdSets.get(chatId);

      // O(1) duplicate check via Set instead of O(n) .some()
      const isDuplicate = idSet.has(message.key.id);
      if (!isDuplicate) {
        idSet.add(message.key.id);
        // OPTIMIZATION: Insert message in correct position (binary search)
        // Messages are kept sorted oldest->newest for consistent display
        const msgTimestamp = Number(message.messageTimestamp) || 0;

        // Find insertion point (binary search for large arrays, linear for small)
        let insertIdx = chatMessages.length;
        if (chatMessages.length > 20) {
          // Binary search for large arrays
          let left = 0, right = chatMessages.length;
          while (left < right) {
            const mid = Math.floor((left + right) / 2);
            const midTs = Number(chatMessages[mid].messageTimestamp) || 0;
            if (midTs < msgTimestamp) {
              left = mid + 1;
            } else {
              right = mid;
            }
          }
          insertIdx = left;
        } else {
          // Linear search for small arrays (faster for small n)
          for (let i = chatMessages.length - 1; i >= 0; i--) {
            const ts = Number(chatMessages[i].messageTimestamp) || 0;
            if (ts <= msgTimestamp) {
              insertIdx = i + 1;
              break;
            }
          }
        }

        chatMessages.splice(insertIdx, 0, message);
      }

      // Prevent memory exhaustion
      if (chatMessages.length > MAX_MESSAGES_PER_CHAT) {
        const oldMsg = chatMessages.shift();
        if (oldMsg.key?.id) {
          messageStore.delete(oldMsg.key.id);
          messageToChatIndex.delete(oldMsg.key.id);
          idSet.delete(oldMsg.key.id);
        }
      }

      // Audio transcription with Whisper + Pre-conversion for Symbian
      if (message.message?.audioMessage) {
        try {
          console.log("Downloading audio for processing...");
          const audioBuffer = await downloadMediaMessage(message, "buffer", {}, {
            logger,
            reuploadRequest: sock?.updateMediaMessage
          });

          // Pre-convert to MP3 for Symbian (background, don't await)
          preConvertAudio(message.key.id, audioBuffer).catch(err => {
            console.error("[PreConvert] Audio background conversion failed:", err.message);
          });

          if (transcriptionEnabled) {
            const maxSize = 10 * 1024 * 1024;
            if (audioBuffer.length > maxSize) {
              message.transcription = "[Audio troppo lungo per la trascrizione]";
            } else {
              const WHISPER_TIMEOUT_MS = 60_000;
              const transcription = await Promise.race([
                transcribeAudioWithWhisper(audioBuffer, 'auto'),
                new Promise((_, rej) => setTimeout(() => rej(new Error('Transcription timeout')), WHISPER_TIMEOUT_MS))
              ]);
              message.transcription = transcription;

              // Send WAP Push notification with transcription (only for messages < 10 minutes old)
              if (transcription && !message.key.fromMe) {
                const messageAge = Date.now() - (Number(message.messageTimestamp) * 1000);
                const TEN_MINUTES = 10 * 60 * 1000;

                if (messageAge <= TEN_MINUTES) {
                  const senderName = message.pushName || chatId.split('@')[0];
                  const notificationText = `[AUDIO] ${senderName}: ${transcription}`;
                  const wmlPath = `/wml/chat.wml?jid=${encodeURIComponent(chatId)}`;

                  if (userSettings.wapPushEnabled && userSettings.wapPushPhone) {
                    const expireMs = userSettings.wapPushExpireEnabled ? userSettings.wapPushExpireMs : 0;
                    const result = await sendWAPPushNotification(userSettings.wapPushPhone, notificationText, wmlPath, 'signal-high', expireMs);

                    // Add to history and manage limit
                    if (result.success && result.wapsiid) {
                      if (userSettings.wapPushHistoryEnabled) {
                        await manageWAPPushHistory(userSettings.wapPushPhone, result.wapsiid, notificationText, new Date());
                      }
                      if (userSettings.wapPushDeleteEnabled && expireMs > 0) {
                        scheduleWAPDelete(userSettings.wapPushPhone, result.wapsiid, expireMs / 60000);
                      }
                    }
                  }
                }
              }
            }
          }
        } catch (error) {
          console.error("Audio processing failed:", error);
          message.transcription = "[Trascrizione fallita]";
        }
      }

      // Video pre-conversion for Symbian (background)
      if (message.message?.videoMessage) {
        try {
          console.log("Pre-converting video for Symbian...");
          const videoBuffer = await downloadMediaMessage(message, "buffer", {}, {
            logger,
            reuploadRequest: sock?.updateMediaMessage
          });

          // Pre-convert to 3GP (background, don't await)
          preConvertVideo(message.key.id, videoBuffer).catch(err => {
            console.error("[PreConvert] Video background conversion failed:", err.message);
          });
        } catch (error) {
          console.error("Video pre-conversion failed:", error);
        }
      }

      // Send WAP Push notification for text messages and other types (not audio, not from self, only < 10 minutes old)
      if (!message.key.fromMe && message.message && !message.message.audioMessage) {
        const messageAge = Date.now() - (Number(message.messageTimestamp) * 1000);
        const TEN_MINUTES = 10 * 60 * 1000;

        if (messageAge <= TEN_MINUTES) {
          const senderName = message.pushName || chatId.split('@')[0];
          let messageType = '';
          let messageText = '';
          let wmlPath = `/wml/chat.wml?jid=${encodeURIComponent(chatId)}`;

          if (message.message.conversation) {
            messageType = '[TEXT]';
            messageText = message.message.conversation;
          } else if (message.message.extendedTextMessage?.text) {
            messageType = '[TEXT]';
            messageText = message.message.extendedTextMessage.text;
          } else if (message.message.imageMessage) {
            messageType = '[IMG]';
            messageText = message.message.imageMessage.caption || t('stickers.type_image');
          } else if (message.message.videoMessage) {
            messageType = '[VIDEO]';
            messageText = message.message.videoMessage.caption || 'Video';
          } else if (message.message.documentMessage) {
            messageType = '[DOC]';
            messageText = message.message.documentMessage.fileName || t('stickers.type_document');
          } else if (message.message.stickerMessage) {
            const sticker = message.message.stickerMessage;
            const content = extractMessageContent(message.message);
            const inlineText = extractInlineTextFromContent(content);
            messageType = '[STK]';
            messageText = stickerTextWithOptionalText(sticker, inlineText, false);
            if (message.key?.id) {
              wmlPath = `/wml/media-info.wml?mid=${encodeURIComponent(message.key.id)}&jid=${encodeURIComponent(chatId)}`;
            }
          } else {
            messageType = '[MSG]';
            messageText = t('common.message');
          }

          const notificationText = `${messageType} ${senderName}: ${messageText}`;

          if (userSettings.wapPushEnabled && userSettings.wapPushPhone) {
            const expireMs = userSettings.wapPushExpireEnabled ? userSettings.wapPushExpireMs : 0;
            const result = await sendWAPPushNotification(userSettings.wapPushPhone, notificationText, wmlPath, 'signal-high', expireMs);
            // Add to history and manage limit
            if (result.success && result.wapsiid) {
              if (userSettings.wapPushHistoryEnabled) {
                await manageWAPPushHistory(userSettings.wapPushPhone, result.wapsiid, notificationText, new Date());
              }
              if (userSettings.wapPushDeleteEnabled && expireMs > 0) {
                scheduleWAPDelete(userSettings.wapPushPhone, result.wapsiid, expireMs / 60000);
              }
            }
          }
        }
      }
    }
  }

  if (newMessagesCount > 0) {
    // PERFORMANCE: Invalidate cache when new messages arrive
    perfCache.invalidateChats();
    perfCache.invalidateContacts();

    saveMessages();
    saveChats();
  }
});

 newSock.ev.on("contacts.set", ({ contacts }) => {
  logger.info(`Contacts set: ${contacts.length}`);

  // Single-pass partition instead of 2x O(N) .filter()
  const [jidContacts, lidContacts] = partitionByLid(contacts);

  logger.info(`Processing ${jidContacts.length} JID contacts first, then ${lidContacts.length} LID contacts`);

  // Process JID contacts first
  for (const c of jidContacts) {
    // Transform to new structure if needed
    const contact = {
      id: c.id,
      name: c.name,
      notify: c.notify,
      verifiedName: c.verifiedName,
      phoneNumber: c.phoneNumber,
      lid: c.lid
    };

    // Store with both original ID and formatted JID as keys
    contactStore.set(c.id, contact);
    // Maintain phone→contact index
    const numPart = c.id.replace(/@.*$/, '');
    if (numPart) phoneToContactIndex.set(numPart, c.id);

    // Also store with formatted JID if different
    const formattedJid = formatJid(c.id);
    if (formattedJid !== c.id) {
      contactStore.set(formattedJid, contact);
    }

    // Store with phone number if available
    if (c.phoneNumber) {
      contactStore.set(c.phoneNumber, contact);
      phoneToContactIndex.set(c.phoneNumber, c.id);
    }
  }

  // Then process LID contacts
  for (const c of lidContacts) {
    // Transform to new structure if needed
    const contact = {
      id: c.id,
      name: c.name,
      notify: c.notify,
      verifiedName: c.verifiedName,
      phoneNumber: c.phoneNumber,
      lid: c.lid
    };

    // Store with both original ID and formatted JID as keys
    contactStore.set(c.id, contact);
    // Maintain phone→contact index
    const numPart = c.id.replace(/@.*$/, '');
    if (numPart) phoneToContactIndex.set(numPart, c.id);

    // Also store with formatted JID if different
    const formattedJid = formatJid(c.id);
    if (formattedJid !== c.id) {
      contactStore.set(formattedJid, contact);
    }

    // Store with phone number if available
    if (c.phoneNumber) {
      contactStore.set(c.phoneNumber, contact);
      phoneToContactIndex.set(c.phoneNumber, c.id);
    }
  }

  saveContacts();
});


 newSock.ev.on("contacts.update", (contacts) => {
  for (const c of contacts) {
    if (c.id) {
      const existing = contactStore.get(c.id) || {};
      const updated = {
        ...existing,
        ...c,
        id: c.id
      };
      contactStore.set(c.id, updated);
      // Maintain phone→contact index
      if (updated.phoneNumber) {
        phoneToContactIndex.set(updated.phoneNumber, c.id);
      }
      const numPart = c.id.replace(/@.*$/, '');
      if (numPart) phoneToContactIndex.set(numPart, c.id);
    }
  }

  // PERFORMANCE: Invalidate contacts cache when contacts change
  if (contacts.length > 0) {
    perfCache.invalidateContacts();
  }
});

// Add LID mapping event handler
newSock.ev.on('lid-mapping.update', (update) => {
  console.log('New LID/PN mapping:', update);
  
  // Update your contact store with this mapping
  if (update.lid && update.pn) {
    const existingContact = contactStore.get(update.lid);
    if (existingContact) {
      contactStore.set(update.lid, {
        ...existingContact,
        phoneNumber: update.pn
      });
    }
  }
});

    newSock.ev.on("chats.set", ({ chats }) => {
      logger.info(`Chats set: ${chats.length}`);

      // Single-pass partition instead of 2x O(N) .filter()
      const [jidChats, lidChats] = partitionByLid(chats);

      logger.info(`Processing ${jidChats.length} JID chats first, then ${lidChats.length} LID chats`);

      // Process JID chats first
      for (const c of jidChats) {
        if (!chatStore.has(c.id)) {
          chatStore.set(c.id, []);
        }
      }

      // Then process LID chats
      for (const c of lidChats) {
        if (!chatStore.has(c.id)) {
          chatStore.set(c.id, []);
        }
      }

      saveChats();
    });

    newSock.ev.on("chats.update", (chats) => {
      for (const c of chats) {
        if (!chatStore.has(c.id)) {
          chatStore.set(c.id, []);
        }
      }

      // PERFORMANCE: Invalidate chats cache when chats change
      if (chats.length > 0) {
        perfCache.invalidateChats();
        saveChats();
      }
    });
  } catch (error) {
    logger.error("Connection error:", error);
    isConnecting = false; // Reset flag before retry
    setTimeout(connectWithBetterSync, 10000);
  } finally {
    // The isConnecting flag is now reset in the connection.update event handlers:
    // - connection === "open" → reset (connected successfully)
    // - connection === "close" → reset (allows reconnection)
    // - catch block → reset (error during setup)
    // No additional reset needed here since the event handlers cover all paths.
  }
}



async function getContactWithLidSupport(jid, sock) {
  // Check if it's a LID
  if (jid.startsWith('lid:')) {
    const contact = contactStore.get(jid);
    if (contact && contact.phoneNumber) {
      return {
        ...contact,
        displayNumber: contact.phoneNumber
      };
    }
    // Try to get PN from LID mapping
    try {
      const pn = await sock.signalRepository.lidMapping.getPNForLID(jid);
      if (pn) {
        return {
          ...contact,
          phoneNumber: pn,
          displayNumber: pn
        };
      }
    } catch (e) {
      // Silently fail
    }
    return {
      ...contact,
      displayNumber: `LID:${jid.substring(4)}`
    };
  }
  
  // Regular phone number
  return {
    ...contactStore.get(jid),
    displayNumber: jid.replace('@s.whatsapp.net', '')
  };
}

// NOTE: connectWithBetterSync() is now called inside worker #1 only (see cluster worker section)
// This prevents multiple QR codes from being generated by different worker processes

// Keep all existing API endpoints from the original code...
// [Include all /api/ routes here]

// NOTE: gracefulShutdown is defined per-process in the cluster section below
// (master handles worker lifecycle, workers handle data saving + connection cleanup)

process.on("uncaughtException", (error) => {
  logger.error("Uncaught Exception:", error);
  // Don't kill the process - log and continue to keep WhatsApp connection alive
});

process.on("unhandledRejection", (reason, promise) => {
  logger.error("Unhandled Rejection at:", promise, "reason:", reason);
});

// Emergency save before process exit
process.on("beforeExit", async (code) => {
  logger.info(`Process about to exit with code: ${code}`);
  logger.info("⚠️  Performing final emergency save...");
  try {
    await storage.flushQueue();

    // Save everything immediately as final backup
    await storage.saveImmediately("contacts", contactStore);
    await storage.saveImmediately("chats", chatStore);
    await storage.saveImmediately("messages", messageStore);
    await storage.saveImmediately("meta", {
      isFullySynced,
      syncAttempts,
      lastSync: new Date().toISOString(),
      contactsCount: contactStore.size,
      chatsCount: chatStore.size,
      messagesCount: messageStore.size,
    });
    logger.info("✓ Final save completed");
  } catch (error) {
    logger.error("❌ Final save failed:", error);
  }
});

// ============ PRODUCTION-GRADE HEALTH CHECKS & MONITORING ============

// Health check endpoint for load balancers
app.get("/health", (req, res) => {
  const health = {
    status: "healthy",
    timestamp: new Date().toISOString(),
    uptime: process.uptime(),
    memory: process.memoryUsage(),
    whatsapp: {
      connected: !!sock?.authState?.creds,
      state: connectionState,
      synced: isFullySynced
    }
  };

  const statusCode = health.whatsapp.connected ? 200 : 503;
  res.status(statusCode).json(health);
});

// Readiness check for Kubernetes/Docker
app.get("/ready", (req, res) => {
  const ready = !!sock?.authState?.creds && isFullySynced;
  res.status(ready ? 200 : 503).json({
    ready,
    whatsapp: {
      connected: !!sock?.authState?.creds,
      synced: isFullySynced
    }
  });
});

// Liveness check
app.get("/live", (req, res) => {
  res.status(200).json({
    alive: true,
    pid: process.pid,
    worker: cluster.worker?.id || 'master'
  });
});

// Advanced metrics endpoint for monitoring
app.get("/api/metrics", (req, res) => {
  const metrics = {
    server: performanceMetrics.getStats(),
    caches: {
      groups: groupsCache.getStats(),
      contacts: contactsCache.getStats(),
      chats: chatsCache.getStats(),
      messages: messagesCache.getStats()
    },
    cluster: {
      isMaster: cluster.isMaster || cluster.isPrimary,
      isWorker: cluster.isWorker,
      workerId: cluster.worker?.id || null,
      pid: process.pid
    },
    whatsapp: {
      connected: !!sock?.authState?.creds,
      state: connectionState,
      synced: isFullySynced,
      syncAttempts: syncAttempts
    },
    stores: {
      contacts: contactStore.size,
      chats: chatStore.size,
      messages: messageStore.size
    }
  };

  res.json(metrics);
});

// ============ SMART WORKER CLUSTERING ============
// Workers are only needed for CPU-intensive tasks (TTS, media conversion, etc.)
// For simple HTTP requests, 2 workers is optimal for Raspberry Pi 4
//
// WHEN TO INCREASE WORKERS:
// - Add TTS/speech-to-speech processing → 3-4 workers
// - Add image/video conversion → 3-4 workers
// - Add AI/ML processing → 4+ workers
// - High HTTP traffic (>1000 req/min) → 3-4 workers
//
// DEFAULT: 2 workers (Worker #1 = WhatsApp + tasks, Worker #2 = HTTP backup)
if (cluster.isMaster || cluster.isPrimary) {
  const numCPUs = os.cpus().length;
  let isShuttingDown = false;
  let masterShutdownTimer = null;

  // Use 1 worker - WhatsApp socket lives in worker #1 and cannot be shared
  const workers = 1;

  logger.info(`🚀 Master process ${process.pid} starting`);
  logger.info(`💪 Spawning ${workers} worker processes (${numCPUs} CPUs available)`);
  logger.info(`ℹ️  Using ${workers} workers - increase WEB_CONCURRENCY env var for heavy tasks (TTS, media conversion)`);

  // Fork workers
  for (let i = 0; i < workers; i++) {
    cluster.fork();
  }

  // Handle worker crashes - auto-restart for high availability
  cluster.on('exit', (worker, code, signal) => {
    if (isShuttingDown) {
      logger.info(`Worker ${worker.process.pid} exited during shutdown (${signal || code})`);
      const activeWorkers = Object.values(cluster.workers || {}).filter(Boolean).length;
      if (activeWorkers === 0) {
        if (masterShutdownTimer) clearTimeout(masterShutdownTimer);
        logger.info('All workers exited. Master shutting down.');
        process.exit(0);
      }
      return;
    }
    logger.warn(`⚠️  Worker ${worker.process.pid} died (${signal || code}). Restarting...`);
    cluster.fork();
  });

  // Stop restarting workers on shutdown signals and terminate cluster cleanly
  for (const sig of ['SIGTERM', 'SIGINT', 'SIGUSR2']) {
    process.on(sig, () => {
      if (isShuttingDown) return;
      isShuttingDown = true;
      logger.info(`Master ${process.pid} received ${sig}. Draining workers...`);

      cluster.disconnect(() => {
        if (masterShutdownTimer) clearTimeout(masterShutdownTimer);
        logger.info('Cluster disconnected. Master exiting.');
        process.exit(0);
      });

      masterShutdownTimer = setTimeout(() => {
        logger.warn('Master shutdown timeout exceeded. Forcing exit.');
        process.exit(1);
      }, 15000);
      if (typeof masterShutdownTimer.unref === 'function') {
        masterShutdownTimer.unref();
      }
    });
  }

  // Log worker status
  cluster.on('online', (worker) => {
    logger.info(`✓ Worker ${worker.process.pid} is online`);
  });

} else {
  // Worker process - handle actual requests

  // Shared callback for when server is listening
  const onServerListening = () => {
    if (HTTPS_ENABLED) {
      logger.info(`🔒 Worker ${process.pid} - WhatsApp WML Gateway started with HTTPS on port ${HTTPS_PORT}`);
    } else {
      logger.info(`🔥 Worker ${process.pid} - WhatsApp WML Gateway started on port ${port}`);
    }
    logger.info(`Environment: ${NODE_ENV}`);
    logger.info("WML endpoints available at /wml/");
    logger.info("API endpoints available at /api/");

    // Only one worker handles periodic tasks (master-like behavior)
    if (cluster.worker.id === 1) {
      // ============ WHATSAPP CONNECTION (WORKER #1 ONLY) ============
      // Only worker #1 connects to WhatsApp to prevent multiple QR codes
      logger.info(`🔌 Worker #1 - Initiating WhatsApp connection...`);
      connectWithBetterSync();

      // ============ RTSP SERVER FOR SYMBIAN/REALPLAYER ============
      rtspServer = new RTSPServer(RTSP_PORT);
      rtspServer.start();
      logger.info(`📺 RTSP Server started on port ${RTSP_PORT}`);

      // ============ AUTO-DOWNLOAD STICKER PACKS (background) ============
      autoDownloadStickerPacks().catch(e =>
        logger.error("[Stickers] Startup download failed:", e.message)
      );

      // Memory-based cleanup (only when memory usage is high)
      setInterval(() => {
        const memUsage = process.memoryUsage();
        const heapUsedMB = memUsage.heapUsed / 1024 / 1024;
        const heapTotalMB = memUsage.heapTotal / 1024 / 1024;
        const heapPercent = (heapUsedMB / heapTotalMB) * 100;

        logger.info(`Memory usage: ${heapUsedMB.toFixed(2)}MB / ${heapTotalMB.toFixed(2)}MB (${heapPercent.toFixed(1)}%)`);

        // Only cleanup if memory usage exceeds 85% (4GB RAM can handle more)
        if (heapPercent > 85) {
          logger.warn(`High memory usage detected (${heapPercent.toFixed(1)}%), running cleanup...`);
          storage.cleanupOldMessages(messageStore, chatStore, 500); // Keep 500 messages per chat (4GB RAM)

          // Force garbage collection if available
          if (global.gc) {
            global.gc();
            logger.info('Garbage collection forced');
          }
        }
      }, 10 * 60 * 1000); // Check every 10 minutes (less frequent for 4GB system)

      // Periodic save - increased interval to reduce Raspberry Pi I/O load
      setInterval(() => {
        saveAll();
        logger.info("Periodic save completed");
      }, 15 * 60 * 1000); // Every 15 minutes instead of 10
    } else {
      // Other workers don't connect to WhatsApp, they just handle HTTP requests
      logger.info(`📡 Worker #${cluster.worker.id} - Handling HTTP requests only (WhatsApp handled by Worker #1)`);
      logger.info(`💡 Worker #${cluster.worker.id} - Ready for heavy tasks (TTS, media conversion, AI processing)`);
    }
  };

  let server;

  function configureServerTimeouts(srv) {
    srv.timeout = 120000; // 2 minutes
    srv.keepAliveTimeout = 65000; // 65 seconds (must be > load balancer timeout)
    srv.headersTimeout = 66000; // Slightly more than keepAliveTimeout
  }

  if (HTTPS_ENABLED) {
    // ============ HTTPS WITH AUTO LET'S ENCRYPT ============
    // Automatically creates and renews certificates — no external certbot needed

    const certPath = path.join(HTTPS_CERTS_DIR, 'cert.pem');
    const keyPath = path.join(HTTPS_CERTS_DIR, 'key.pem');
    const accountKeyPath = path.join(HTTPS_CERTS_DIR, 'account-key.pem');

    // Ensure certs directory exists
    if (!fs.existsSync(HTTPS_CERTS_DIR)) {
      fs.mkdirSync(HTTPS_CERTS_DIR, { recursive: true });
    }

    // Store pending ACME HTTP-01 challenges (token → keyAuthorization)
    const pendingChallenges = new Map();

    // HTTP server on port 80 — serves ACME challenges + redirects everything else to HTTPS
    const httpServer = http.createServer((req, res) => {
      // ACME HTTP-01 challenge response
      if (req.url.startsWith('/.well-known/acme-challenge/')) {
        const token = req.url.split('/').pop();
        const keyAuth = pendingChallenges.get(token);
        if (keyAuth) {
          res.writeHead(200, { 'Content-Type': 'text/plain' });
          res.end(keyAuth);
          return;
        }
      }
      // Redirect all other HTTP traffic to HTTPS
      const host = req.headers.host?.replace(/:\d+$/, '') || HTTPS_DOMAIN;
      res.writeHead(301, { Location: `https://${host}${HTTPS_PORT === 443 ? '' : ':' + HTTPS_PORT}${req.url}` });
      res.end();
    });
    httpServer.on('error', (err) => {
      if (err.code === 'EACCES') {
        logger.warn('⚠️ Cannot bind port 80 (requires root/admin privileges). ACME HTTP-01 challenges and HTTP→HTTPS redirect will not work.');
        logger.warn('   Run with sudo or use: sudo setcap cap_net_bind_service=+ep $(which node)');
      } else if (err.code === 'EADDRINUSE') {
        logger.warn('⚠️ Port 80 already in use. ACME HTTP-01 challenges and HTTP→HTTPS redirect will not work.');
      } else {
        logger.error('❌ HTTP server (port 80) error:', err.message);
      }
    });
    httpServer.listen(80, () => {
      logger.info('🔀 HTTP server on port 80 (ACME challenges + HTTPS redirect)');
    });

    // Request or renew certificate via ACME protocol
    async function obtainCertificate() {
      logger.info(`🔐 Requesting Let's Encrypt certificate for ${HTTPS_DOMAIN}...`);

      // Generate or load account key (persisted for reuse)
      let accountKey;
      if (fs.existsSync(accountKeyPath)) {
        accountKey = fs.readFileSync(accountKeyPath);
      } else {
        accountKey = await acme.crypto.createPrivateKey();
        fs.writeFileSync(accountKeyPath, accountKey);
      }

      const client = new acme.Client({
        directoryUrl: acme.directory.letsencrypt.production,
        accountKey,
      });

      // Register account (idempotent — reuses existing if already registered)
      await client.createAccount({
        termsOfServiceAgreed: true,
        contact: [`mailto:${HTTPS_EMAIL}`],
      });

      // Generate CSR + private key for the domain
      const [domainKey, csr] = await acme.crypto.createCsr({
        commonName: HTTPS_DOMAIN,
      });

      // Request certificate with HTTP-01 challenge
      const cert = await client.auto({
        csr,
        email: HTTPS_EMAIL,
        termsOfServiceAgreed: true,
        challengeCreateFn: async (authz, challenge, keyAuthorization) => {
          if (challenge.type === 'http-01') {
            pendingChallenges.set(challenge.token, keyAuthorization);
          }
        },
        challengeRemoveFn: async (authz, challenge) => {
          if (challenge.type === 'http-01') {
            pendingChallenges.delete(challenge.token);
          }
        },
        challengePriority: ['http-01'],
      });

      // Save certificate files
      fs.writeFileSync(keyPath, domainKey);
      fs.writeFileSync(certPath, cert);
      logger.info(`✅ Let's Encrypt certificate saved to ${HTTPS_CERTS_DIR}`);

      return { key: domainKey, cert };
    }

    // Check if existing certificates are valid and not expiring within 30 days
    function certsNeedRenewal() {
      try {
        if (!fs.existsSync(certPath) || !fs.existsSync(keyPath)) {
          return true; // No certs exist — need to create
        }
        const certPem = fs.readFileSync(certPath, 'utf8');
        // Parse "Not After" from the certificate using openssl-style parsing
        const cert = new crypto.X509Certificate(certPem);
        const expiryDate = new Date(cert.validTo);
        const daysLeft = (expiryDate - Date.now()) / (1000 * 60 * 60 * 24);
        logger.info(`📜 Certificate expires: ${expiryDate.toISOString()} (${Math.floor(daysLeft)} days left)`);
        return daysLeft < 30; // Renew if less than 30 days left
      } catch (err) {
        logger.warn('⚠️  Could not read existing certificate, will create new one:', err.message);
        return true;
      }
    }

    // Obtain or renew certs, then start HTTPS server
    async function startHttpsServer() {
      let tlsKey, tlsCert;

      if (certsNeedRenewal()) {
        const result = await obtainCertificate();
        tlsKey = result.key;
        tlsCert = result.cert;
      } else {
        tlsKey = fs.readFileSync(keyPath);
        tlsCert = fs.readFileSync(certPath);
      }

      server = https.createServer({ key: tlsKey, cert: tlsCert }, app);
      configureServerTimeouts(server);
      server.listen(HTTPS_PORT, onServerListening);

      server.on("error", (error) => {
        if (error.code === "EADDRINUSE") {
          logger.error(`Port ${HTTPS_PORT} is already in use`);
          process.exit(1);
        } else {
          logger.error("Server error:", error);
          process.exit(1);
        }
      });

      // Auto-renew: check every 12 hours, renew if expiring within 30 days
      setInterval(async () => {
        try {
          if (certsNeedRenewal()) {
            logger.info('🔄 Certificate expiring soon, auto-renewing...');
            const result = await obtainCertificate();
            server.setSecureContext({ key: result.key, cert: result.cert });
            logger.info('✅ Certificate auto-renewed and hot-reloaded (zero downtime)');
          }
        } catch (renewErr) {
          logger.error('❌ Certificate auto-renewal failed:', renewErr.message);
        }
      }, 12 * 60 * 60 * 1000); // Every 12 hours
    }

    startHttpsServer().catch((err) => {
      logger.error('❌ Failed to start HTTPS server:', err.message);
      logger.info('⚠️  Falling back to HTTP on port ' + port);
      server = app.listen(port, onServerListening);
      configureServerTimeouts(server);
      server.on("error", (error) => {
        if (error.code === "EADDRINUSE") {
          logger.error(`Port ${port} is already in use`);
          process.exit(1);
        } else {
          logger.error("Server error:", error);
          process.exit(1);
        }
      });
    });
  } else {
    // ============ PLAIN HTTP (DEFAULT) ============
    server = app.listen(port, onServerListening);
    configureServerTimeouts(server);

    server.on("error", (error) => {
      if (error.code === "EADDRINUSE") {
        logger.error(`Port ${port} is already in use`);
        process.exit(1);
      } else {
        logger.error("Server error:", error);
        process.exit(1);
      }
    });
  }

  // ============ PRODUCTION-GRADE GRACEFUL SHUTDOWN ============
  // Handles SIGTERM and SIGINT for zero-downtime deployments
  let isShuttingDown = false;

  const gracefulShutdown = async (signal) => {
    if (isShuttingDown) return;
    isShuttingDown = true;

    logger.info(`\n⚠️  ${signal} received - initiating graceful shutdown`);

    // Stop accepting new connections
    server.close(async () => {
      logger.info("✓ HTTP server closed - no longer accepting connections");

      // Close WhatsApp connection
      if (sock) {
        logger.info("Closing WhatsApp connection...");
        sock.end();
      }

      // Save all data IMMEDIATELY (not queued)
      logger.info("Saving all data...");
      try {
        // Flush any queued saves first
        logger.info("Flushing queued saves...");
        await storage.flushQueue();

        // Use saveImmediately instead of queueSave to avoid delays
        await storage.saveImmediately("contacts", contactStore);
        await storage.saveImmediately("chats", chatStore);
        await storage.saveImmediately("messages", messageStore);
        await storage.saveImmediately("meta", {
          isFullySynced,
          syncAttempts,
          lastSync: new Date().toISOString(),
          contactsCount: contactStore.size,
          chatsCount: chatStore.size,
          messagesCount: messageStore.size,
        });
        logger.info("✓ All data saved successfully");
      } catch (error) {
        logger.error("Error saving data during shutdown:", error);
      }

      // Close HTTP agent connections
      if (axiosAgent) {
        axiosAgent.destroy();
        logger.info("✓ HTTP connections closed");
      }

      logger.info("✅ Graceful shutdown complete");
      process.exit(0);
    });

    // Force shutdown after 30 seconds
    setTimeout(async () => {
      logger.error("❌ Forced shutdown - graceful shutdown timeout exceeded");
      logger.info("⚠️  Attempting emergency data save...");
      try {
        await storage.flushQueue();

        // Use saveImmediately for emergency save
        await storage.saveImmediately("contacts", contactStore);
        await storage.saveImmediately("chats", chatStore);
        await storage.saveImmediately("messages", messageStore);
        await storage.saveImmediately("meta", {
          isFullySynced,
          syncAttempts,
          lastSync: new Date().toISOString(),
          contactsCount: contactStore.size,
          chatsCount: chatStore.size,
          messagesCount: messageStore.size,
        });
        logger.info("✓ Emergency save completed");
      } catch (error) {
        logger.error("❌ Emergency save failed:", error);
      }
      process.exit(1);
    }, 30000);
  };

  // Handle shutdown signals
  process.on("SIGTERM", () => gracefulShutdown("SIGTERM"));
  process.on("SIGINT", () => gracefulShutdown("SIGINT"));

}

// ============ FAVICON ENDPOINTS ============
// Serve WhatsApp-style favicon for all browsers (SVG → cached buffer)
app.get("/favicon.svg", (req, res) => {
  if (!_faviconBuffer) _faviconBuffer = Buffer.from(WAP_FAVICON_SVG);
  res.setHeader("Content-Type", "image/svg+xml");
  res.setHeader("Cache-Control", "public, max-age=86400");
  res.send(_faviconBuffer);
});
app.get("/favicon.ico", (req, res) => {
  // Redirect .ico requests to SVG — avoids generating ICO binary
  res.redirect(301, "/favicon.svg");
});

// Initialize connection
app.get("/api/status", (req, res) => {
  const isConnected = !!sock?.authState?.creds;

  res.json({
    connected: isConnected,
    status: connectionState,
    user: sock?.user || null,
    qrAvailable: !!currentQR,
    syncStatus: {
      isFullySynced,
      syncAttempts,
      contactsCount: contactStore.size,
      chatsCount: chatStore.size,
      messagesCount: messageStore.size,
    },
    uptime: process.uptime(),
    recommendations: getRecommendations(isConnected),
  });
});

app.get("/api/status-detailed", async (req, res) => {
  try {
    const isConnected = !!sock?.authState?.creds;
    let syncStatus = {
      contacts: contactStore.size,
      chats: chatStore.size,
      messages: messageStore.size,
      isFullySynced,
      syncAttempts,
    };

    res.json({
      connected: isConnected,
      status: connectionState,
      user: sock?.user || null,
      qrAvailable: !!currentQR,
      syncStatus,
      stores: {
        contactStore: {
          size: contactStore.size,
          sample: Array.from(contactStore.entries())
            .slice(0, 3)
            .map(([key, value]) => ({
              key,
              name: value.name || value.notify || "Unknown",
              hasName: !!value.name,
            })),
        },
        chatStore: {
          size: chatStore.size,
          sample: Array.from(chatStore.keys()).slice(0, 5),
        },
      },
      recommendations: getRecommendations(isConnected),
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// Performance monitoring endpoint - cluster and system metrics
app.get("/api/performance", (req, res) => {
  const memUsage = process.memoryUsage();
  const cpuUsage = process.cpuUsage();

  res.json({
    cluster: {
      isMaster: cluster.isMaster || cluster.isPrimary,
      isWorker: cluster.isWorker,
      workerId: cluster.worker?.id || null,
      workerPid: process.pid,
      totalWorkers: cluster.isMaster ? Object.keys(cluster.workers || {}).length : null,
    },
    system: {
      cpus: os.cpus().length,
      platform: os.platform(),
      arch: os.arch(),
      totalMemory: `${(os.totalmem() / 1024 / 1024 / 1024).toFixed(2)} GB`,
      freeMemory: `${(os.freemem() / 1024 / 1024 / 1024).toFixed(2)} GB`,
      loadAverage: os.loadavg(),
    },
    process: {
      uptime: `${Math.floor(process.uptime())} seconds`,
      memory: {
        rss: `${(memUsage.rss / 1024 / 1024).toFixed(2)} MB`,
        heapTotal: `${(memUsage.heapTotal / 1024 / 1024).toFixed(2)} MB`,
        heapUsed: `${(memUsage.heapUsed / 1024 / 1024).toFixed(2)} MB`,
        external: `${(memUsage.external / 1024 / 1024).toFixed(2)} MB`,
      },
      cpu: {
        user: `${(cpuUsage.user / 1000).toFixed(2)} ms`,
        system: `${(cpuUsage.system / 1000).toFixed(2)} ms`,
      },
    },
    optimization: {
      clustering: cluster.isMaster || cluster.isWorker,
      nonBlocking: true,
      asyncIO: true,
      multiCore: true,
    },
    stores: {
      contacts: contactStore.size,
      chats: chatStore.size,
      messages: messageStore.size,
    },
  });
});

function getRecommendations(isConnected) {
  if (!isConnected) {
    return ["Please connect to WhatsApp first", "Check QR code if available"];
  }

  if (!isFullySynced && contactStore.size === 0 && chatStore.size === 0) {
    return [
      "Try calling POST /api/full-sync to force data loading",
      "Wait a few more seconds for WhatsApp to sync",
      "Send a test message to trigger data loading",
    ];
  }

  if (contactStore.size === 0) {
    return ["Call POST /api/force-sync-contacts to load contacts"];
  }

  if (chatStore.size === 0) {
    return ["Call POST /api/force-sync-chats to load chats"];
  }

  return ["All systems operational"];
}

// Force sync endpoints
app.post("/api/full-sync", async (req, res) => {
  try {
    if (!sock) return res.status(500).json({ error: "Not connected" });

    console.log("🔄 Starting full manual sync...");
    const results = {
      contacts: 0,
      chats: 0,
      recentChats: 0,
      errors: [],
    };

    // Sync contacts
    try {
      console.log("📞 Attempting contact sync...");

      // In Baileys, contacts are populated automatically via events
      // We can't manually fetch them, so we wait for the events
      if (contactStore.size === 0) {
        console.log("📞 Waiting for contacts to sync via events...");
        await delay(3000); // Wait for events to populate
      }

      results.contacts = contactStore.size;
      console.log(`📞 Contacts available: ${contactStore.size}`);
    } catch (error) {
      results.errors.push(`Contacts sync info: ${error.message}`);
    }

    // Sync chats
    try {
      const chats = await sock.groupFetchAllParticipating();
      Object.keys(chats).forEach((chatId) => {
        if (!chatStore.has(chatId)) {
          chatStore.set(chatId, []);
        }
      });
      results.chats = Object.keys(chats).length;
      console.log(`💬 Manually synced ${Object.keys(chats).length} chats`);
    } catch (error) {
      results.errors.push(`Chats sync failed: ${error.message}`);
    }

    // Sync recent chats
    try {
      console.log("💬 Checking for additional chats...");

      // In Baileys, we don't have fetchChats, but we have what we got from groupFetchAllParticipating
      // Let's wait a bit more for any chat events
      await delay(2000);

      results.recentChats = chatStore.size - results.chats;
      console.log(`💬 Additional chats found: ${results.recentChats}`);
    } catch (error) {
      results.errors.push(`Additional chats check failed: ${error.message}`);
    }

    // Update sync status
    if (contactStore.size > 0 || chatStore.size > 0) {
      isFullySynced = true;
    }

    res.json({
      status: "completed",
      results,
      currentStore: {
        contacts: contactStore.size,
        chats: chatStore.size,
        messages: messageStore.size,
      },
      isFullySynced,
    });
  } catch (error) {
    console.error("❌ Full sync failed:", error);
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/force-sync-contacts", async (req, res) => {
  try {
    if (!sock) return res.status(500).json({ error: "Not connected" });

    console.log("🔄 Checking contact sync status...");

    // In Baileys, contacts are synced via events, not direct API calls
    // We can only report what we have and potentially trigger a refresh
    const initialCount = contactStore.size;

    // Wait a bit to see if more contacts come in
    console.log("📞 Waiting for contact events...");
    await delay(3000);

    const finalCount = contactStore.size;
    const newContacts = finalCount - initialCount;

    console.log(
      `✅ Contact sync check completed. Total: ${finalCount}, New: ${newContacts}`
    );

    res.json({
      status: "success",
      message: "Contacts are synced via WhatsApp events",
      initialCount,
      finalCount,
      newContacts,
      totalInStore: contactStore.size,
    });
  } catch (error) {
    console.error("❌ Contact sync check failed:", error);
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/force-sync-chats", async (req, res) => {
  try {
    if (!sock) return res.status(500).json({ error: "Not connected" });

    console.log("🔄 Forcing chat sync...");

    const initialChatCount = chatStore.size;

    // Get participating groups (this works)
    const chats = await sock.groupFetchAllParticipating();

    Object.keys(chats).forEach((chatId) => {
      if (!chatStore.has(chatId)) {
        chatStore.set(chatId, []);
      }
    });

    // Wait for any additional chat events
    console.log("💬 Waiting for additional chat events...");
    await delay(3000);

    const finalChatCount = chatStore.size;
    const newChats = finalChatCount - initialChatCount;

    console.log(
      `✅ Chat sync completed. Groups: ${
        Object.keys(chats).length
      }, Total: ${finalChatCount}`
    );

    res.json({
      status: "success",
      groupChats: Object.keys(chats).length,
      initialTotal: initialChatCount,
      finalTotal: finalChatCount,
      newChats: newChats,
      totalInStore: chatStore.size,
    });
  } catch (error) {
    console.error("❌ Force sync chats failed:", error);
    res.status(500).json({ error: error.message });
  }
});

app.get("/api/debug-stores", (req, res) => {
  res.json({
    connectionState,
    isFullySynced,
    syncAttempts,
    contactStore: {
      size: contactStore.size,
      sample: Array.from(contactStore.entries())
        .slice(0, 5)
        .map(([key, value]) => ({
          key,
          name: value.name || value.notify || "Unknown",
          hasName: !!value.name,
          notify: value.notify,
          verifiedName: value.verifiedName,
        })),
    },
    chatStore: {
      size: chatStore.size,
      chats: Array.from(chatStore.keys()).slice(0, 10),
    },
    messageStore: {
      size: messageStore.size,
      sample: Array.from(messageStore.keys()).slice(0, 5),
    },
  });
});

// =================== QR CODE ENDPOINTS ===================

app.get("/api/qr", (req, res) => {
  if (currentQR) {
    res.send(`
            <html><head>${WAP_FAVICON_LINK}</head><body style="text-align:center;padding:50px;font-family:Arial;">
                <h2>📱 WhatsApp QR Code</h2>
                <div style="background:white;padding:20px;border-radius:10px;display:inline-block;">
                    <img src="data:image/png;base64,${Buffer.from(
                      currentQR
                    ).toString(
                      "base64"
                    )}" style="border:10px solid #25D366;border-radius:10px;"/>
                </div>
                <p>Scan with WhatsApp app</p>
                <p><small>Auto-refresh in 10 seconds</small></p>
                <script>setTimeout(() => location.reload(), 10000);</script>
            </body></html>
        `);
  } else {
    res.json({
      message: "QR not available",
      connected: !!sock?.authState?.creds,
      status: connectionState,
    });
  }
});

app.get("/api/qr/image", async (req, res) => {
  const { format = "png" } = req.query;

  if (!currentQR) {
    // Return a placeholder image instead of JSON to prevent "unknown response" errors
    const placeholderText = `No QR Code\nStatus: ${connectionState}\nPlease wait...`;

    try {
      // Generate a simple text-based QR placeholder
      const qrBuffer = await QRCode.toBuffer(placeholderText, {
        type: "png",
        width: 256,
        margin: 2,
        color: {
          dark: "#666666",
          light: "#FFFFFF",
        },
      });

      res.setHeader("Content-Type", format === "wbmp" ? "image/vnd.wap.wbmp" : "image/png");
      res.setHeader("Cache-Control", "no-cache");
      return res.send(qrBuffer);
    } catch (err) {
      // Ultimate fallback: 1x1 transparent PNG
      const transparentPng = Buffer.from(
        "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==",
        "base64"
      );
      res.setHeader("Content-Type", "image/png");
      return res.send(transparentPng);
    }
  }

  try {
    if (format.toLowerCase() === "wbmp") {
      // Generate QR as WBMP format using qrcode library
      try {
        const qrBuffer = await QRCode.toBuffer(currentQR, {
          type: "png",
          width: 256,
          margin: 2,
          color: {
            dark: "#000000",
            light: "#FFFFFF",
          },
        });

        // Convert PNG to simple WBMP-like format
        // WBMP is a monochrome format, so we'll return the QR as minimal binary
        res.setHeader("Content-Type", "image/vnd.wap.wbmp");
        res.setHeader("Content-Disposition", 'inline; filename="qr-code.wbmp"');
        res.setHeader("Cache-Control", "no-cache");

        // Return the buffer (simplified WBMP representation)
        res.send(qrBuffer);
      } catch (qrError) {
        // Fallback: return raw QR string as WBMP
        res.setHeader("Content-Type", "image/vnd.wap.wbmp");
        res.setHeader("Content-Disposition", 'inline; filename="qr-code.wbmp"');
        const qrBuffer = Buffer.from(currentQR, "utf8");
        res.send(qrBuffer);
      }
    } else if (format.toLowerCase() === "base64") {
      // Return as base64 JSON response
      res.json({
        qrCode: currentQR,
        format: "base64",
        timestamp: Date.now(),
        dataUrl: `data:text/plain;base64,${Buffer.from(currentQR).toString(
          "base64"
        )}`,
      });
    } else if (format.toLowerCase() === "png") {
      // Generate proper PNG QR code - small size for WAP devices
      try {
        const qrBuffer = await QRCode.toBuffer(currentQR, {
          type: "png",
          width: 128,  // Reduced from 256 to 128 for WAP compatibility
          margin: 1,   // Reduced margin
          color: {
            dark: "#000000",
            light: "#FFFFFF",
          },
        });

        // Further compress with sharp for WAP compatibility (like video frames)
        const compressedBuffer = await sharp(qrBuffer)
          .resize(96, 96, { fit: 'contain' })  // Even smaller for old phones
          .png({ quality: 70, compressionLevel: 9 })
          .toBuffer();

        res.setHeader("Content-Type", "image/png");
        res.setHeader("Content-Disposition", 'inline; filename="qr-code.png"');
        res.setHeader("Cache-Control", "no-cache");
        res.send(compressedBuffer);
      } catch (qrError) {
        // Fallback to base64 if available
        res.setHeader("Content-Type", "image/png");
        res.send(Buffer.from(currentQR, "base64"));
      }
    } else if (format.toLowerCase() === "svg") {
      // Generate SVG QR code
      try {
        const qrSvg = await QRCode.toString(currentQR, {
          type: "svg",
          width: 256,
          margin: 2,
          color: {
            dark: "#000000",
            light: "#FFFFFF",
          },
        });

        res.setHeader("Content-Type", "image/svg+xml");
        res.setHeader("Content-Disposition", 'inline; filename="qr-code.svg"');
        res.setHeader("Cache-Control", "no-cache");
        res.send(qrSvg);
      } catch (qrError) {
        res.status(500).json({ error: "Failed to generate SVG QR code" });
      }
    } else {
      res.status(400).json({
        error: "Unsupported format",
        supportedFormats: ["png", "svg", "base64", "wbmp"],
        examples: [
          "GET /api/qr/image?format=png",
          "GET /api/qr/image?format=svg",
          "GET /api/qr/image?format=wbmp",
          "GET /api/qr/image?format=base64",
        ],
      });
    }
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// Generate QR code as true WBMP format (like video frames)
app.get("/api/qr/wbmp", async (req, res) => {
  if (!currentQR) {
    // Return a 1x1 black WBMP
    const header = Buffer.from([0x00, 0x00, 0x01, 0x01]);
    const data = Buffer.from([0x00]);
    return res
      .setHeader("Content-Type", "image/vnd.wap.wbmp")
      .setHeader("Cache-Control", "no-cache")
      .send(Buffer.concat([header, data]));
  }

  try {
    // Generate QR code as PNG first
    const qrBuffer = await QRCode.toBuffer(currentQR, {
      type: "png",
      width: 200,
      margin: 2,
      color: {
        dark: "#000000",
        light: "#FFFFFF",
      },
    });

    // Convert to WBMP - EXTREMELY small for very old phones (32x32 minimum)
    const { data: pixels, info } = await sharp(qrBuffer)
      .greyscale()
      .resize(32, 32, {  // Tiny - 32x32 pixels (absolute minimum for old phones)
        kernel: sharp.kernel.nearest,  // Preserves QR block patterns
        fit: "contain",
        position: "center",
        background: { r: 255, g: 255, b: 255, alpha: 1 },
      })
      .threshold(128, { greyscale: true, grayscale: true })
      .raw()
      .toBuffer({ resolveWithObject: true });

    // Create WBMP header
    const width = info.width;
    const height = info.height;
    const header = Buffer.from([
      0x00, // Type 0
      0x00, // FixHeaderField
      width,
      height,
    ]);

    // Convert pixels to WBMP 1-bit format
    // WBMP spec: 0 = black, 1 = white (inverted from usual bitmap)
    const rowBytes = Math.ceil(width / 8);
    const wbmpData = Buffer.alloc(rowBytes * height);

    // Initialize all bits to 1 (white)
    wbmpData.fill(0xFF);

    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const pixelIndex = y * width + x;
        const pixel = pixels[pixelIndex];
        const isBlack = pixel < 128;

        if (isBlack) {
          // Set bit to 0 for black pixels
          const byteIndex = y * rowBytes + Math.floor(x / 8);
          const bitIndex = 7 - (x % 8);
          wbmpData[byteIndex] &= ~(1 << bitIndex);
        }
      }
    }

    const wbmpBuffer = Buffer.concat([header, wbmpData]);

    res.setHeader("Content-Type", "image/vnd.wap.wbmp");
    res.setHeader("Cache-Control", "no-cache");
    res.send(wbmpBuffer);
  } catch (error) {
    console.error("QR WBMP generation error:", error);
    // Fallback to 1x1 black WBMP
    const header = Buffer.from([0x00, 0x00, 0x01, 0x01]);
    const data = Buffer.from([0x00]);
    res
      .setHeader("Content-Type", "image/vnd.wap.wbmp")
      .setHeader("Cache-Control", "no-cache")
      .send(Buffer.concat([header, data]));
  }
});

// QR as text page (WML friendly)
app.get("/wml/qr-text.wml", (req, res) => {
  if (!currentQR) {
    const body = `
      <p>QR code not available</p>
      <p>
        <a href="/wml/qr.wml">Back to QR page</a>
      </p>
    `;
    return sendWml(res, card("qr-text", "QR Text", body));
  }

  // Split QR into chunks for better display
  const chunkSize = 40;
  const chunks = [];
  for (let i = 0; i < currentQR.length; i += chunkSize) {
    chunks.push(currentQR.substring(i, i + chunkSize));
  }

  const body = `
    <p>QR Code as Text:</p>
    <p><small>${chunks.map((chunk, i) => `${i + 1}. ${esc(chunk)}`).join('<br/>')}</small></p>
    <p>Length: ${currentQR.length} chars</p>
    <p>
      <a href="/wml/qr.wml">Back</a>
    </p>
  `;

  sendWml(res, card("qr-text", "QR Text", body));
});

// QR as WAP-friendly image embedded in page (viewable directly on WAP devices)
app.get("/wml/qr-wap.wml", (req, res) => {
  if (!currentQR) {
    const body = `
      <p>${t('qr.connecting')}</p>
      <p>${t('qr.status')} ${esc(connectionState)}</p>
      <p>
        <a href="/wml/qr-wap.wml">${t('qr.refresh')}</a>
      </p>
      <p>
        <a href="/wml/qr.wml">${t('common.back')}</a>
      </p>
    `;
    return sendWml(res, card("qr-wap", "QR WAP", body));
  }

  // Detect old WAP phones vs modern browsers
  const ua = (req.headers['user-agent'] || '').toLowerCase();
  const isOldPhone = ua.includes('nokia') || ua.includes('up.browser') || ua.includes('openwave') || ua.includes('mot-') || ua.includes('sie-') || ua.includes('sam-') || ua.includes('sec-') || ua.includes('series40');
  const qrSize = isOldPhone ? 60 : 200;

  const body = `
    <p align="center">
      <img src="/api/qr/image?format=png" alt="QR Code" width="${qrSize}" height="${qrSize}"/>
    </p>
    <p align="center"><a href="/wml/qr-wap.wml">${t('qr.refresh')}</a> | <a href="/wml/qr.wml">${t('common.back')}</a></p>
    <do type="accept" label="${t('common.refresh')}">
      <go href="/wml/qr-wap.wml"/>
    </do>
  `;

  sendWml(res, card("qr-wap", "QR WAP", body));
});

// Pairing code page - link phone number instead of scanning QR
app.get("/wml/pairing.wml", (req, res) => {
  const isConnected = !!sock?.authState?.creds && connectionState === 'open';

  if (isConnected) {
    const body = `
      <p align="center">${t('qr.connected')}</p>
      <p align="center"><a href="/wml/home.wml">${t('qr.go_home')}</a></p>
    `;
    return sendWml(res, card("pairing", t('pairing.title'), body));
  }

  if (currentPairingCode) {
    const body = `
      <p align="center"><b>${t('pairing.code_label')}</b></p>
      <p align="center"><b>${esc(currentPairingCode)}</b></p>
      <p align="center">${t('pairing.open_whatsapp')}</p>
      <p align="center">${esc(t('pairing.instructions'))}</p>
      <p align="center">${t('pairing.enter_code')}</p>
      <p align="center">
        <a href="/wml/pairing.wml">${t('qr.refresh')}</a> | <a href="/wml/qr.wml">${t('common.back')}</a>
      </p>
    `;
    return sendWml(res, card("pairing", t('pairing.code_title'), body));
  }

  const body = `
    <p align="center"><b>${t('pairing.link_phone_title')}</b></p>
    <p align="center">${t('pairing.enter_number')}</p>
    <p>
      <input name="phone" type="text" format="*N" title="${t('pairing.phone_input')}"/>
    </p>
    <p align="center">
      <anchor>${t('pairing.request_code')}
        <go href="/wml/pairing-request.wml" method="post">
          <postfield name="phone" value="$(phone)"/>
        </go>
      </anchor>
    </p>
    <p align="center">
      <a href="/wml/qr.wml">${t('common.back')}</a>
    </p>
  `;

  sendWml(res, card("pairing", t('pairing.title'), body));
});

// Process pairing code request
app.post("/wml/pairing-request.wml", async (req, res) => {
  const phone = (req.body?.phone || '').replace(/\D/g, '');

  if (!phone || phone.length < 8) {
    const body = `
      <p align="center">${t('pairing.invalid_number')}</p>
      <p align="center">${t('pairing.enter_full_number')}</p>
      <p align="center"><a href="/wml/pairing.wml">${t('common.back')}</a></p>
    `;
    return sendWml(res, card("pairing-err", t('pairing.error_title'), body));
  }

  if (!sock) {
    const body = `
      <p align="center">${t('pairing.not_connected')}</p>
      <p align="center"><a href="/wml/pairing.wml">${t('qr.refresh')}</a></p>
    `;
    return sendWml(res, card("pairing-err", t('pairing.error_title'), body));
  }

  try {
    const code = await sock.requestPairingCode(phone);
    currentPairingCode = code;
    currentQR = null;
    logger.info(`Pairing code generated via WAP: ${code} (for phone ${phone})`);

    const body = `
      <p align="center"><b>${t('pairing.code_label')}</b></p>
      <p align="center"><b>${esc(code)}</b></p>
      <p align="center">${t('pairing.open_whatsapp')}</p>
      <p align="center">${esc(t('pairing.instructions'))}</p>
      <p align="center">${t('pairing.enter_code')}</p>
      <p align="center">
        <a href="/wml/pairing.wml">${t('qr.refresh')}</a> | <a href="/wml/qr.wml">${t('common.back')}</a>
      </p>
    `;
    sendWml(res, card("pairing-ok", t('pairing.code_title'), body));
  } catch (err) {
    logger.error(`Pairing code request failed: ${err.message}`);
    const body = `
      <p align="center">${t('pairing.error_prefix')} ${esc(err.message)}</p>
      <p align="center"><a href="/wml/pairing.wml">${t('pairing.retry')}</a></p>
    `;
    sendWml(res, card("pairing-err", t('pairing.error_title'), body));
  }
});

app.get("/api/qr/text", (req, res) => {
  if (!currentQR) {
    return sendRawWmlAware(res, `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN"
  "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
  <card id="noqr" title="QR Not Available">
    <p>QR code not available</p>
  </card>
</wml>`);
  }

  sendRawWmlAware(res, `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN"
  "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
  <card id="qr" title="WhatsApp QR">
    <p>Your QR string:</p>
    <p>${currentQR}</p>
  </card>
</wml>`);
});

app.post("/api/logout", async (req, res) => {
  try {
    // Save data IMMEDIATELY before logout
    logger.info("Saving all data before logout...");
    await storage.saveImmediately("contacts", contactStore);
    await storage.saveImmediately("chats", chatStore);
    await storage.saveImmediately("messages", messageStore);
    await storage.saveImmediately("meta", {
      isFullySynced,
      syncAttempts,
      lastSync: new Date().toISOString(),
      contactsCount: contactStore.size,
      chatsCount: chatStore.size,
      messagesCount: messageStore.size,
    });

    if (sock) await sock.logout();
    if (fs.existsSync("./auth_info_baileys")) {
      fs.rmSync("./auth_info_baileys", { recursive: true });
    }

    // DO NOT clear stores - keep data persistent
    // contactStore.clear();
    // chatStore.clear();
    // messageStore.clear();
    isFullySynced = false;
    syncAttempts = 0;

    res.json({ status: "Logged out - data saved" });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.get("/api/me", async (req, res) => {
  try {
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const profilePic = await sock
      .profilePictureUrl(sock.user.id)
      .catch(() => null);
    const status = await sock.fetchStatus(sock.user.id).catch(() => null);

    res.json({
      user: sock.user,
      profilePicture: profilePic,
      status: status?.status,
      syncStatus: {
        isFullySynced,
        contactsCount: contactStore.size,
        chatsCount: chatStore.size,
      },
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/update-profile-name", async (req, res) => {
  try {
    const { name } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    await sock.updateProfileName(name);
    res.json({ status: "Profile name updated" });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/update-profile-status", async (req, res) => {
  try {
    const { status } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    await sock.updateProfileStatus(status);
    res.json({ status: "Profile status updated" });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/update-profile-picture", async (req, res) => {
  try {
    const { imageUrl } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const response = await axios.get(imageUrl, { responseType: "arraybuffer" });
    await sock.updateProfilePicture(sock.user.id, response.data);
    res.json({ status: "Profile picture updated" });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/presence", async (req, res) => {
  try {
    const { jid, presence = "available" } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    if (jid) {
      await sock.sendPresenceUpdate(presence, formatJid(jid));
    } else {
      await sock.sendPresenceUpdate(presence);
    }
    res.json({ status: `Presence set to ${presence}` });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// =================== ENHANCED CONTACTS ENDPOINTS ===================

app.get("/api/contacts/all", async (req, res) => {
  try {
    if (!sock) return res.status(500).json({ error: "Not connected" });

    // Auto-sync if no contacts and not synced yet
    if (contactStore.size === 0 && !isFullySynced) {
      console.log("📞 No contacts found, waiting for sync events...");
      // In Baileys, contacts come via events, so we just wait
      await delay(2000);
      console.log(`📞 Contacts after wait: ${contactStore.size}`);
    }

    const { page = 1, limit = 100, enriched = false } = req.query;

    // ULTRA-PERFORMANCE: Use pre-sorted cache (instant response)
    perfCache.getSortedContacts(contactStore, chatStore);

    // Get paginated contacts instantly (no sorting needed!)
    const startIndex = (parseInt(page) - 1) * parseInt(limit);
    const endIndex = startIndex + parseInt(limit);
    const paginatedContacts = perfCache.sortedContacts
      .slice(startIndex, endIndex)
      .map(c => c.contact);
    const totalContacts = perfCache.sortedContacts.length;

    if (enriched === "true") {
      // ULTRA-PERFORMANCE: Parallelize API calls for all contacts at once
      // Instead of sequential (contact1 -> contact2 -> contact3)
      // Do parallel: (contact1 + contact2 + contact3) all at once
      const enrichedContacts = await Promise.all(
        paginatedContacts.map(async (contact) => {
          try {
            // Run all 3 API calls in parallel for this contact
            const [profilePic, status, businessProfile] = await Promise.all([
              sock.profilePictureUrl(contact.id, "image").catch(() => null),
              sock.fetchStatus(contact.id).catch(() => null),
              sock.getBusinessProfile(contact.id).catch(() => null),
            ]);

            return {
              id: contact.id,
              name: contact.name || contact.notify || contact.verifiedName,
              profilePicture: profilePic,
              status: status?.status,
              lastSeen: status?.setAt,
              isMyContact: contact.name ? true : false,
              isBusiness: !!businessProfile,
              businessProfile: businessProfile,
              notify: contact.notify,
              verifiedName: contact.verifiedName,
            };
          } catch (error) {
            return {
              id: contact.id,
              name: contact.name || contact.notify || contact.verifiedName,
              error: error.message,
            };
          }
        })
      );

      res.json({
        contacts: enrichedContacts,
        pagination: {
          page: parseInt(page),
          limit: parseInt(limit),
          total: totalContacts,
          totalPages: Math.ceil(totalContacts / parseInt(limit)),
          hasNext: endIndex < totalContacts,
          hasPrev: parseInt(page) > 1,
        },
        syncInfo: { isFullySynced, syncAttempts },
      });
    } else {
      const basicContacts = paginatedContacts.map((contact) => ({
        id: contact.id,
        name: contact.name || contact.notify || contact.verifiedName,
        notify: contact.notify,
        verifiedName: contact.verifiedName,
        isMyContact: contact.name ? true : false,
      }));

      res.json({
        contacts: basicContacts,
        pagination: {
          page: parseInt(page),
          limit: parseInt(limit),
          total: totalContacts,
          totalPages: Math.ceil(totalContacts / parseInt(limit)),
          hasNext: endIndex < totalContacts,
          hasPrev: parseInt(page) > 1,
        },
        syncInfo: { isFullySynced, syncAttempts },
      });
    }
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.get("/api/contacts/count", (req, res) => {
  try {
    if (!sock) return res.status(500).json({ error: "Not connected" });

    // Single pass O(N) instead of two separate O(N) filter+count passes
    let withNames = 0, businessContacts = 0;
    for (const c of contactStore.values()) {
      if (c.name) withNames++;
      if (c.verifiedName) businessContacts++;
    }
    res.json({
      totalContacts: contactStore.size,
      withNames,
      businessContacts,
      syncInfo: { isFullySynced, syncAttempts },
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/contacts/search", async (req, res) => {
  try {
    const { query, limit = 50 } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });
    if (!query || query.length < 2) {
      return res
        .status(400)
        .json({ error: "Query must be at least 2 characters" });
    }

    const searchQuery = query.toLowerCase();

    // ULTRA-PERFORMANCE: Use pre-sorted cache (instant response)
    perfCache.getSortedContacts(contactStore, chatStore);

    // Filter using pre-built search index (instant)
    const filtered = perfCache.sortedContacts.filter((c) =>
      c.searchText.includes(searchQuery)
    );

    const results = filtered.slice(0, parseInt(limit)).map(c => c.contact);

    res.json({
      query: query,
      results: results.map((contact) => ({
        id: contact.id,
        name: contact.name || contact.notify || contact.verifiedName,
        notify: contact.notify,
        verifiedName: contact.verifiedName,
        number: contact.id.replace("@s.whatsapp.net", ""),
        isMyContact: contact.name ? true : false,
      })),
      total: results.length,
      syncInfo: { isFullySynced, syncAttempts },
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// =================== ENHANCED CHAT ENDPOINTS ===================

app.get("/api/chats/with-numbers", async (req, res) => {
  try {
    if (!sock) return res.status(500).json({ error: "Not connected" });

    // Auto-sync if no chats and not synced yet
    if (chatStore.size === 0 && !isFullySynced) {
      console.log("💬 No chats found, attempting auto-sync...");
      try {
        const chats = await sock.groupFetchAllParticipating();

        Object.keys(chats).forEach((chatId) => {
          if (!chatStore.has(chatId)) {
            chatStore.set(chatId, []);
          }
        });

        console.log(`💬 Auto-synced ${Object.keys(chats).length} group chats`);

        // Wait for additional chat events
        await delay(2000);
        console.log(`💬 Total chats after wait: ${chatStore.size}`);
      } catch (syncError) {
        console.log("⚠️ Auto-sync failed:", syncError.message);
      }
    }

    // Build directly from iterator instead of Array.from() allocation
    const chats = [];
    let directChatsCount = 0, groupChatsCount = 0;
    for (const chatId of chatStore.keys()) {
      const messages = chatStore.get(chatId) || [];
      const lastMessage = messages[messages.length - 1];
      const contact = contactStore.get(chatId);

      const phoneNumber = chatId
        .replace("@s.whatsapp.net", "")
        .replace("@g.us", "");
      const isGroup = chatId.endsWith("@g.us");
      if (isGroup) groupChatsCount++;
      else directChatsCount++;

      chats.push({
        id: chatId,
        phoneNumber: isGroup ? null : phoneNumber,
        groupId: isGroup ? phoneNumber : null,
        isGroup: isGroup,
        contact: {
          name: contact?.name || contact?.notify || contact?.verifiedName,
          isMyContact: contact?.name ? true : false,
        },
        messageCount: messages.length,
        lastMessage: lastMessage
          ? {
              id: lastMessage.key.id,
              message: extractMessageContent(lastMessage.message),
              timestamp: lastMessage.messageTimestamp,
              fromMe: lastMessage.key.fromMe,
            }
          : null,
      });
    }

    chats.sort((a, b) => {
      const aTime = a.lastMessage?.timestamp || 0;
      const bTime = b.lastMessage?.timestamp || 0;
      return bTime - aTime;
    });

    res.json({
      chats,
      total: chats.length,
      directChats: directChatsCount,
      groupChats: groupChatsCount,
      syncInfo: { isFullySynced, syncAttempts },
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.get("/api/chat/by-number/:number", async (req, res) => {
  try {
    const { number } = req.params;
    const { limit = 50, offset = 0 } = req.query;

    if (!sock) return res.status(500).json({ error: "Not connected" });

    const jid = formatJid(number);
    const messages = chatStore.get(jid) || [];

    const contact = contactStore.get(jid);
    const profilePic = await sock.profilePictureUrl(jid).catch(() => null);
    const status = await sock.fetchStatus(jid).catch(() => null);

    // Pagination
    const startIndex = Math.max(
      0,
      messages.length - parseInt(limit) - parseInt(offset)
    );
    const endIndex = messages.length - parseInt(offset);
    const paginatedMessages = messages.slice(startIndex, endIndex);

    const formattedMessages = paginatedMessages.map((msg) => ({
      id: msg.key.id,
      fromMe: msg.key.fromMe,
      timestamp: msg.messageTimestamp,
      message: extractMessageContent(msg.message),
      messageType: getContentType(msg.message),
      quoted: msg.message?.extendedTextMessage?.contextInfo?.quotedMessage
        ? true
        : false,
    }));

    res.json({
      number: number,
      jid: jid,
      contact: {
        name: contact?.name || contact?.notify || contact?.verifiedName,
        profilePicture: profilePic,
        status: status?.status,
        lastSeen: status?.setAt,
        isMyContact: contact?.name ? true : false,
      },
      chat: {
        messages: formattedMessages,
        total: messages.length,
        showing: formattedMessages.length,
        hasMore: startIndex > 0,
        isGroup: jid.endsWith("@g.us"),
      },
      syncInfo: { isFullySynced, syncAttempts },
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.get("/api/chat/exists/:number", (req, res) => {
  try {
    const { number } = req.params;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const jid = formatJid(number);
    const messages = chatStore.get(jid) || [];
    const contact = contactStore.get(jid);

    res.json({
      number: number,
      jid: jid,
      exists: messages.length > 0,
      messageCount: messages.length,
      hasContact: !!contact,
      contactName: contact?.name || contact?.notify || contact?.verifiedName,
      lastActivity:
        messages.length > 0
          ? messages[messages.length - 1].messageTimestamp
          : null,
      syncInfo: { isFullySynced, syncAttempts },
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.get("/api/chat/stats/:number", async (req, res) => {
  try {
    const { number } = req.params;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const jid = formatJid(number);
    const messages = chatStore.get(jid) || [];
    const contact = contactStore.get(jid);

    if (messages.length === 0) {
      return res.json({
        number: number,
        jid: jid,
        exists: false,
        message: "No chat history found",
        syncInfo: { isFullySynced, syncAttempts },
      });
    }

    // Single-pass statistics instead of 3x O(M) .filter() + 1x O(M) .forEach()
    const MEDIA_TYPES = new Set(['imageMessage', 'videoMessage', 'audioMessage', 'documentMessage', 'stickerMessage']);
    let myMessagesCount = 0, theirMessagesCount = 0, mediaMessagesCount = 0;
    const messageTypes = {};
    for (const msg of messages) {
      if (msg.key.fromMe) myMessagesCount++;
      else theirMessagesCount++;
      const type = getContentType(msg.message) || 'unknown';
      messageTypes[type] = (messageTypes[type] || 0) + 1;
      if (MEDIA_TYPES.has(type)) mediaMessagesCount++;
    }

    const firstMessage = messages[0];
    const lastMessage = messages[messages.length - 1];

    res.json({
      number: number,
      jid: jid,
      contact: {
        name: contact?.name || contact?.notify || contact?.verifiedName,
        isMyContact: contact?.name ? true : false,
      },
      statistics: {
        totalMessages: messages.length,
        myMessages: myMessagesCount,
        theirMessages: theirMessagesCount,
        mediaMessages: mediaMessagesCount,
        messageTypes: messageTypes,
        firstMessage: {
          timestamp: firstMessage.messageTimestamp,
          fromMe: firstMessage.key.fromMe,
        },
        lastMessage: {
          timestamp: lastMessage.messageTimestamp,
          fromMe: lastMessage.key.fromMe,
        },
        chatDuration:
          lastMessage.messageTimestamp - firstMessage.messageTimestamp,
      },
      syncInfo: { isFullySynced, syncAttempts },
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/chats/bulk-by-numbers", async (req, res) => {
  try {
    const { numbers, includeMessages = false, messageLimit = 10 } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });
    if (!Array.isArray(numbers)) {
      return res.status(400).json({ error: "Numbers must be an array" });
    }

    const results = [];

    for (const number of numbers) {
      try {
        const jid = formatJid(number);
        const messages = chatStore.get(jid) || [];
        const contact = contactStore.get(jid);

        const result = {
          number: number,
          jid: jid,
          exists: messages.length > 0,
          messageCount: messages.length,
          contact: {
            name: contact?.name || contact?.notify || contact?.verifiedName,
            isMyContact: contact?.name ? true : false,
          },
        };

        if (includeMessages && messages.length > 0) {
          const recentMessages = messages.slice(-parseInt(messageLimit));
          result.recentMessages = recentMessages.map((msg) => ({
            id: msg.key.id,
            fromMe: msg.key.fromMe,
            timestamp: msg.messageTimestamp,
            message: extractMessageContent(msg.message),
            messageType: getContentType(msg.message),
          }));
        }

        results.push(result);
      } catch (error) {
        results.push({
          number: number,
          error: error.message,
        });
      }
    }

    // Single pass O(N) instead of three separate O(N) filter passes
    let withChats = 0, withoutChats = 0, errors = 0;
    for (const r of results) {
      if (r.error) errors++;
      else if (r.exists) withChats++;
      else withoutChats++;
    }
    res.json({
      results,
      total: results.length,
      withChats,
      withoutChats,
      errors,
      syncInfo: { isFullySynced, syncAttempts },
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// =================== OTHER ENDPOINTS ===================

app.get("/api/contacts", async (req, res) => {
  try {
    if (!sock) return res.status(500).json({ error: "Not connected" });

    // Build from iterator + top-50 partial sort instead of full O(N log N) sort
    const allContacts = [];
    for (const c of contactStore.values()) {
      const msgs = chatStore.get(c.id) || [];
      const lastMsg = msgs.length > 0 ? msgs[msgs.length - 1] : null;
      c._sortTs = lastMsg ? Number(lastMsg.messageTimestamp) : 0;
      allContacts.push(c);
    }

    const contacts = topK(allContacts, 50, (a, b) => b._sortTs - a._sortTs);

    const enrichedContacts = [];
    for (const contact of contacts) {
      try {
        const profilePic = await sock
          .profilePictureUrl(contact.id, "image")
          .catch(() => null);
        const status = await sock.fetchStatus(contact.id).catch(() => null);

        enrichedContacts.push({
          id: contact.id,
          name: contact.name || contact.notify || contact.verifiedName,
          profilePicture: profilePic,
          status: status?.status,
          isMyContact: contact.name ? true : false,
          lastSeen: status?.setAt,
        });

        await delay(100);
      } catch (error) {
        enrichedContacts.push({
          id: contact.id,
          name: contact.name || contact.notify || contact.verifiedName,
          error: error.message,
        });
      }
    }

    res.json({
      contacts: enrichedContacts,
      total: contactStore.size,
      showing: enrichedContacts.length,
      syncInfo: { isFullySynced, syncAttempts },
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.get("/api/chats", async (req, res) => {
  try {
    if (!sock) return res.status(500).json({ error: "Not connected" });

    // Build directly from iterator instead of Array.from() allocation
    const chats = [];
    for (const chatId of chatStore.keys()) {
      const messages = chatStore.get(chatId) || [];
      const lastMessage = messages[messages.length - 1];

      chats.push({
        id: chatId,
        isGroup: chatId.endsWith("@g.us"),
        messageCount: messages.length,
        lastMessage: lastMessage
          ? {
              id: lastMessage.key.id,
              message: extractMessageContent(lastMessage.message),
              timestamp: lastMessage.messageTimestamp,
              fromMe: lastMessage.key.fromMe,
            }
          : null,
      });
    }

    chats.sort((a, b) => {
      const aTime = a.lastMessage?.timestamp || 0;
      const bTime = b.lastMessage?.timestamp || 0;
      return bTime - aTime;
    });

    res.json({
      chats,
      total: chats.length,
      syncInfo: { isFullySynced, syncAttempts },
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.get("/api/messages/:jid", async (req, res) => {
  try {
    const { jid } = req.params;
    const { limit = 50, offset = 0 } = req.query;

    if (!sock) return res.status(500).json({ error: "Not connected" });

    const formattedJid = formatJid(jid);
    const messages = chatStore.get(formattedJid) || [];

    const startIndex = Math.max(
      0,
      messages.length - parseInt(limit) - parseInt(offset)
    );
    const endIndex = messages.length - parseInt(offset);
    const paginatedMessages = messages.slice(startIndex, endIndex);

    const formattedMessages = paginatedMessages.map((msg) => ({
      id: msg.key.id,
      fromMe: msg.key.fromMe,
      timestamp: msg.messageTimestamp,
      message: extractMessageContent(msg.message),
      messageType: getContentType(msg.message),
      quoted: msg.message?.extendedTextMessage?.contextInfo?.quotedMessage
        ? true
        : false,
    }));

    res.json({
      jid: formattedJid,
      messages: formattedMessages,
      total: messages.length,
      showing: formattedMessages.length,
      hasMore: startIndex > 0,
      syncInfo: { isFullySynced, syncAttempts },
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/search-messages", async (req, res) => {
  try {
    const { query, jid, limit = 50 } = req.body;

    if (!sock) return res.status(500).json({ error: "Not connected" });
    if (!query || query.length < 2) {
      return res
        .status(400)
        .json({ error: "Query must be at least 2 characters" });
    }

    const results = [];
    const searchQuery = query.toLowerCase();

    // Use iterator directly instead of Array.from() + cached search text
    const chatsToSearch = jid ? [formatJid(jid)] : chatStore.keys();

    for (const chatId of chatsToSearch) {
      const messages = chatStore.get(chatId) || [];

      for (const msg of messages) {
        // Use cached lowercase text for faster repeated searches
        const cachedText = getMessageSearchText(msg);
        if (!cachedText.includes(searchQuery)) continue;

        const content = extractMessageContent(msg.message);
        const msgText =
          content?.conversation ||
          content?.extendedTextMessage?.text ||
          content?.imageMessage?.caption ||
          content?.videoMessage?.caption ||
          "";

        results.push({
          chatId,
          messageId: msg.key.id,
          fromMe: msg.key.fromMe,
          timestamp: msg.messageTimestamp,
          message: msgText,
          messageType: getContentType(msg.message),
        });

        if (results.length >= limit) break;
      }

      if (results.length >= limit) break;
    }
    trimSearchTextCache();

    results.sort((a, b) => b.timestamp - a.timestamp);

    res.json({
      query: query,
      results,
      total: results.length,
      syncInfo: { isFullySynced, syncAttempts },
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// Update business profile handling for LIDs
app.get("/api/contact/:jid", async (req, res) => {
  try {
    const { jid } = req.params;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const formattedJid = formatJid(jid);
    let profilePic, status, businessProfile;

    try {
      profilePic = await sock.profilePictureUrl(formattedJid).catch(() => null);
      status = await sock.fetchStatus(formattedJid).catch(() => null);
      businessProfile = await sock.getBusinessProfile(formattedJid).catch(() => null);
    } catch (e) {
      // Silent fail for optional features
    }

    res.json({
      jid: formattedJid,
      profilePicture: profilePic,
      status: status?.status,
      businessProfile,
      addressingMode: sock.getMessageAddressingMode(formattedJid),
      syncInfo: { isFullySynced, syncAttempts },
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/block/:jid", async (req, res) => {
  try {
    const { jid } = req.params;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    await sock.updateBlockStatus(formatJid(jid), "block");
    res.json({ status: "Contact blocked" });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/unblock/:jid", async (req, res) => {
  try {
    const { jid } = req.params;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    await sock.updateBlockStatus(formatJid(jid), "unblock");
    res.json({ status: "Contact unblocked" });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// Update check-numbers endpoint
app.post("/api/check-numbers", async (req, res) => {
  try {
    const { numbers } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const results = [];
    for (const number of numbers) {
      try {
        // Check if it's a LID - skip onWhatsApp for LIDs
        const isLid = number.startsWith('lid:');

        if (isLid) {
          // LIDs cannot be checked with onWhatsApp
          results.push({
            number,
            exists: false,
            error: "LID identifiers cannot be checked with onWhatsApp",
          });
        } else {
          // Clean the number - remove non-digits and plus
          const cleanedNumber = number.replace(/\D/g, '');

          // Use cleaned number directly (no domain)
          const exists = await sock.onWhatsApp([cleanedNumber]);

          results.push({
            number,
            cleanedNumber,
            exists: exists.length > 0,
            details: exists[0] || null,
          });
        }
      } catch (error) {
        results.push({
          number,
          error: error.message,
        });
      }
      await delay(500);
    }

    res.json({ results });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});
// =================== SEND MESSAGE ENDPOINTS ===================

app.post("/api/send-text", async (req, res) => {
  try {
    const { to, message } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const result = await sock.sendMessage(formatJid(to), { text: message });
    res.json({ status: "ok", messageId: result.key.id });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/send-image", async (req, res) => {
  try {
    const { to, imageUrl, caption } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const response = await axios.get(imageUrl, { responseType: "arraybuffer" });
    const result = await sock.sendMessage(formatJid(to), {
      image: response.data,
      caption,
    });
    res.json({ status: "ok", messageId: result.key.id });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/send-video", async (req, res) => {
  try {
    const { to, videoUrl, caption } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const response = await axios.get(videoUrl, { responseType: "arraybuffer" });
    const result = await sock.sendMessage(formatJid(to), {
      video: response.data,
      caption,
    });
    res.json({ status: "ok", messageId: result.key.id });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/send-audio", async (req, res) => {
  try {
    const { to, audioUrl, ptt = false } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const response = await axios.get(audioUrl, { responseType: "arraybuffer" });
    const result = await sock.sendMessage(formatJid(to), {
      audio: response.data,
      ptt,
      mimetype: "audio/mp4",
    });
    res.json({ status: "ok", messageId: result.key.id });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/send-document", async (req, res) => {
  try {
    const { to, documentUrl, fileName, mimetype } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const response = await axios.get(documentUrl, {
      responseType: "arraybuffer",
      timeout: 120000, // 120 second timeout for documents
      maxContentLength: 100 * 1024 * 1024, // 100MB max
      maxBodyLength: 100 * 1024 * 1024
    });
    const result = await sock.sendMessage(formatJid(to), {
      document: response.data,
      fileName: fileName || "document",
      mimetype: mimetype || "application/octet-stream",
    });
    res.json({ status: "ok", messageId: result.key.id });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/send-sticker", async (req, res) => {
  try {
    const { to, imageUrl } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const response = await axios.get(imageUrl, { responseType: "arraybuffer" });
    const result = await sock.sendMessage(formatJid(to), {
      sticker: response.data,
    });
    res.json({ status: "ok", messageId: result.key.id });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/send-location", async (req, res) => {
  try {
    const { to, latitude, longitude, name } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const result = await sock.sendMessage(formatJid(to), {
      location: {
        degreesLatitude: parseFloat(latitude),
        degreesLongitude: parseFloat(longitude),
        name,
      },
    });
    res.json({ status: "ok", messageId: result.key.id });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/send-contact", async (req, res) => {
  try {
    const { to, contacts } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const contactList = Array.isArray(contacts) ? contacts : [contacts];
    const vCards = contactList.map((contact) => ({
      displayName: contact.name,
      vcard: `BEGIN:VCARD\nVERSION:3.0\nFN:${contact.name}\nTEL;type=CELL:${contact.number}\nEND:VCARD`,
    }));

    const result = await sock.sendMessage(formatJid(to), {
      contacts: {
        displayName: `${contactList.length} contact${
          contactList.length > 1 ? "s" : ""
        }`,
        contacts: vCards,
      },
    });
    res.json({ status: "ok", messageId: result.key.id });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/send-poll", async (req, res) => {
  try {
    const { to, name, values, selectableCount = 1 } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const result = await sock.sendMessage(formatJid(to), {
      poll: {
        name,
        values,
        selectableCount: Math.min(selectableCount, values.length),
      },
    });
    res.json({ status: "ok", messageId: result.key.id });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/send-reaction", async (req, res) => {
  try {
    const { to, messageId, emoji } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const targetMessage = messageStore.get(messageId);
    if (!targetMessage) {
      return res.status(404).json({ error: "Message not found" });
    }

    const result = await sock.sendMessage(formatJid(to), {
      react: {
        text: emoji,
        key: targetMessage.key,
      },
    });
    res.json({ status: "ok", messageId: result.key.id });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/send-reply", async (req, res) => {
  try {
    const { to, message, quotedMessageId } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const quotedMessage = messageStore.get(quotedMessageId);
    if (!quotedMessage) {
      return res.status(404).json({ error: "Quoted message not found" });
    }

    const result = await sock.sendMessage(
      formatJid(to),
      { text: message },
      { quoted: quotedMessage }
    );
    res.json({ status: "ok", messageId: result.key.id });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/forward-message", async (req, res) => {
  try {
    const { messageId, to } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const targetMessage = messageStore.get(messageId);
    if (!targetMessage) {
      return res.status(404).json({ error: "Message not found" });
    }

    const recipients = Array.isArray(to) ? to : [to];
    const results = [];

    for (const recipient of recipients) {
      try {
        const result = await sock.relayMessage(
          formatJid(recipient),
          targetMessage.message,
          {}
        );
        results.push({
          recipient: formatJid(recipient),
          status: "sent",
          messageId: result.key.id,
        });
      } catch (error) {
        results.push({
          recipient: formatJid(recipient),
          status: "failed",
          error: error.message,
        });
      }
      await delay(1000);
    }

    res.json({ status: "ok", results });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.delete("/api/delete-message", async (req, res) => {
  try {
    const { messageId, to } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const targetMessage = messageStore.get(messageId);
    if (!targetMessage) {
      return res.status(404).json({ error: "Message not found" });
    }

    await sock.sendMessage(formatJid(to), { delete: targetMessage.key });
    res.json({ status: "ok" });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

/*
app.post("/api/read-messages", async (req, res) => {
  // ⚠️ CRITICAL BAN PREVENTION (Baileys 7.x)
  // Read receipts (ACKs) are DISABLED to prevent WhatsApp bans
  // DO NOT re-enable without understanding the ban risks
  try {
    return res.status(403).json({
      error: "Read receipts disabled for ban prevention",
      warning: "Sending read receipts can trigger WhatsApp bans in Baileys 7.x",
      suggestion: "Do not re-enable this feature"
    });

    // DISABLED CODE (kept for reference):
    // const { messageIds } = req.body;
    // if (!sock) return res.status(500).json({ error: "Not connected" });
    //
    // const keys = messageIds
    //   .map((id) => {
    //     const msg = messageStore.get(id);
    //     return msg ? msg.key : null;
    //   })
    //   .filter(Boolean);
    //
    // if (keys.length === 0) {
    //   return res.status(404).json({ error: "No valid messages found" });
    // }
    //
    // await sock.readMessages(keys);
    // res.json({ status: "ok", markedAsRead: keys.length });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});*/

// =================== GROUP MANAGEMENT ===================

app.post("/api/group-create", async (req, res) => {
  try {
    const { name, participants } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const participantJids = participants.map((jid) => formatJid(jid));
    const group = await sock.groupCreate(name, participantJids);

    res.json({ status: "ok", groupId: group.id });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.get("/api/groups", async (req, res) => {
  try {
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const groups = await sock.groupFetchAllParticipating();
    res.json({ groups: Object.values(groups) });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.get("/api/group/:groupId/metadata", async (req, res) => {
  try {
    const { groupId } = req.params;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const metadata = await sock.groupMetadata(groupId);
    res.json({ group: metadata });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// Update group participant handling to work with LIDs
app.post("/api/group/:groupId/participants", async (req, res) => {
  try {
    const { groupId } = req.params;
    const { participants, action } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    // Participants can now be LIDs or PNs
    const participantJids = participants.map(jid => {
      // If it's already a JID (with domain), use as-is
      if (jid.includes('@')) return jid;
      // If it's a LID, use as-is
      if (jid.startsWith('lid:')) return jid;
      // Otherwise, format as phone number
      return formatJid(jid);
    });

    const result = await sock.groupParticipantsUpdate(
      groupId,
      participantJids,
      action
    );

    res.json({ status: "ok", result });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/group/:groupId/subject", async (req, res) => {
  try {
    const { groupId } = req.params;
    const { subject } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    await sock.groupUpdateSubject(groupId, subject);
    res.json({ status: "ok" });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/group/:groupId/description", async (req, res) => {
  try {
    const { groupId } = req.params;
    const { description } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    await sock.groupUpdateDescription(groupId, description);
    res.json({ status: "ok" });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/group/:groupId/settings", async (req, res) => {
  try {
    const { groupId } = req.params;
    const { setting, value } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    await sock.groupSettingUpdate(groupId, setting, value);
    res.json({ status: "ok" });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.get("/api/group/:groupId/invite-code", async (req, res) => {
  try {
    const { groupId } = req.params;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const code = await sock.groupInviteCode(groupId);
    res.json({
      inviteCode: code,
      inviteUrl: `https://chat.whatsapp.com/${code}`,
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/group/:groupId/revoke-invite", async (req, res) => {
  try {
    const { groupId } = req.params;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const newCode = await sock.groupRevokeInvite(groupId);
    res.json({
      status: "ok",
      newInviteCode: newCode,
      newInviteUrl: `https://chat.whatsapp.com/${newCode}`,
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/group/:groupId/leave", async (req, res) => {
  try {
    const { groupId } = req.params;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    await sock.groupLeave(groupId);
    res.json({ status: "ok" });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// =================== MEDIA & UTILITIES ===================

// Update media download/upload for LID support
app.post("/api/download-media", async (req, res) => {
  try {
    const { messageId } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const message = messageStore.get(messageId);
    if (!message) {
      return res.status(404).json({ error: "Message not found" });
    }

    const contentType = getContentType(message.message);
    if (![
      "imageMessage",
      "videoMessage",
      "audioMessage",
      "documentMessage",
    ].includes(contentType)) {
      return res.status(400).json({ error: "No downloadable media" });
    }

    // Updated download with proper options
    const mediaData = await downloadMediaMessage(
      message, 
      "buffer", 
      {}, 
      {
        logger,
        reuploadRequest: sock.updateMediaMessage
      }
    );

    if (!mediaData) {
      return res.status(400).json({ error: "Failed to download media" });
    }

    // Rest of the media handling code...
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.get("/api/privacy", async (req, res) => {
  try {
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const privacy = await sock.fetchPrivacySettings();
    res.json({ privacySettings: privacy });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/privacy", async (req, res) => {
  try {
    const { setting, value } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    await sock.updatePrivacySettings({ [setting]: value });
    res.json({ status: "ok" });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/send-status", async (req, res) => {
  try {
    const { type, content } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    let statusMessage = {};

    if (type === "text") {
      statusMessage = { text: content };
    } else if (type === "image") {
      const response = await axios.get(content, {
        responseType: "arraybuffer",
      });
      statusMessage = { image: response.data };
    } else if (type === "video") {
      const response = await axios.get(content, {
        responseType: "arraybuffer",
      });
      statusMessage = { video: response.data };
    }

    const result = await sock.sendMessage("status@broadcast", statusMessage);
    res.json({ status: "ok", messageId: result.key.id });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post("/api/send-broadcast", async (req, res) => {
  try {
    const { message, recipients, delay: msgDelay = 2000 } = req.body;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    const results = [];

    for (let i = 0; i < recipients.length; i++) {
      try {
        const result = await sock.sendMessage(formatJid(recipients[i]), {
          text: message,
        });
        results.push({
          recipient: formatJid(recipients[i]),
          status: "sent",
          messageId: result.key.id,
        });

        if (i < recipients.length - 1) {
          await delay(parseInt(msgDelay));
        }
      } catch (error) {
        results.push({
          recipient: formatJid(recipients[i]),
          status: "failed",
          error: error.message,
        });
      }
    }

    res.json({ status: "ok", results });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// API endpoint per servire profile picture in tutti i formati con WBMP AD ALTISSIMA FEDELTA
 // Complete Profile Management System for WML Interface
// Enhanced Me/Profile page with full functionality

app.get("/wml/me.wml", async (req, res) => {
  try {
    if (!sock) {
      sendWml(
        res,
        resultCard("Error", ["Not connected to WhatsApp"], "/wml/home.wml")
      );
      return;
    }

    const user = sock.user;
    let status = null;

    try {
      status = await sock.fetchStatus(user.id).catch(() => null);
    } catch (e) {
      // Silent fail for optional features
    }

    const body = `
      <p><b>${t('profile.title')}</b></p>
      <p>${t('profile.name')} <b>${esc(user?.name || user?.notify || "Unknown")}</b></p>
      <p>${t('profile.number')} ${esc(
        user?.id?.replace("@s.whatsapp.net", "") || "Unknown"
      )}</p>
      <p>${t('profile.jid')} <small>${esc(user?.id || "Unknown")}</small></p>
      ${
        status
          ? `<p>${t('profile.status')} <em>${esc(status.status || t('profile.no_status'))}</em></p>`
          : `<p>${t('profile.status')} <em>${t('profile.no_status')}</em></p>`
      }
      ${
        status?.setAt
          ? `<p><small>${t('profile.updated')} ${new Date(
              status.setAt
            ).toLocaleString()}</small></p>`
          : ""
      }

      <p><b>${t('profile.actions')}</b></p>
      <p>
        <a href="/wml/profile.edit-name.wml" accesskey="1">${t('profile.edit_name')}</a><br/>
        <a href="/wml/profile.edit-status.wml" accesskey="2">${t('profile.edit_status')}</a><br/>
        <a href="/wml/profile.picture.wml" accesskey="3">${t('profile.view_picture')}</a><br/>
      </p>

      <p><b>${t('profile.account_info')}</b></p>
      <p>${t('profile.connected')} ${esc(connectionState)}</p>
      <p>${t('profile.sync_status')} ${isFullySynced ? t('profile.complete') : t('profile.in_progress')}</p>
      <p>${t('profile.data')} ${contactStore.size} ${t('profile.contacts')}, ${chatStore.size} ${t('profile.chats')}</p>
      <p>${t('profile.messages')} ${messageStore.size} ${t('profile.stored')}</p>
      <p>${t('profile.uptime')} ${Math.floor(process.uptime() / 60)} ${t('profile.minutes')}</p>

      ${navigationBar()}

      <do type="accept" label="${t('profile.edit_name')}">
        <go href="/wml/profile.edit-name.wml"/>
      </do>
      <do type="options" label="${t('common.refresh')}">
        <go href="/wml/me.wml"/>
      </do>
    `;

    sendWml(res, card("me", t('profile.title'), body));
  } catch (e) {
    sendWml(
      res,
      resultCard(
        "Error",
        [e.message || "Failed to load profile"],
        "/wml/home.wml"
      )
    );
  }
});

// Edit Name page
app.get("/wml/profile.edit-name.wml", (req, res) => {
  if (!sock) {
    sendWml(
      res,
      resultCard("Error", ["Not connected to WhatsApp"], "/wml/me.wml")
    );
    return;
  }

  const user = sock.user;
  const currentName = user?.name || user?.notify || "";
  const success = req.query.success === "1";
  const preset = req.query.preset || "";

  const successMessage = success
    ? `
    <p><b>✓ Name Updated Successfully!</b></p>
    <p></p>
  `
    : "";

  const body = `
    <p><b>Edit Profile Name</b></p>
    ${successMessage}
    
    <p>Current Name: <b>${esc(currentName || "Not set")}</b></p>
    
    <p>New Name:</p>
    <input name="name" title="Your name" value="${esc(
      preset || currentName
    )}" size="25" maxlength="25"/>
    
    <p><small>Max 25 characters. This is your display name on WhatsApp.</small></p>
    
    <p>
      <anchor title="Update">Update
        <go method="post" href="/wml/profile.update-name">
          <postfield name="name" value="$(name)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.update')}">
      <go method="post" href="/wml/profile.update-name">
        <postfield name="name" value="$(name)"/>
      </go>
    </do>

    <p><b>Quick Names:</b></p>
    <p>
      <a href="/wml/profile.edit-name.wml?preset=${encodeURIComponent(
        currentName
      )}" accesskey="1">[1] Keep Current</a><br/>
      <a href="/wml/profile.edit-name.wml?preset=${encodeURIComponent(
        user?.id?.replace("@s.whatsapp.net", "") || ""
      )}" accesskey="2">[2] Use Number</a><br/>
    </p>
    
    <p>
      <a href="/wml/me.wml" accesskey="0">[0] Back to Profile</a> |
      <a href="/wml/home.wml" accesskey="*">[*] Home</a>
    </p>
    
    <do type="options" label="${t('common.cancel')}">
      <go href="/wml/me.wml"/>
    </do>
  `;

  sendWml(res, card("edit-name", "Edit Name", body));
});

// Edit Status page
app.get("/wml/profile.edit-status.wml", async (req, res) => {
  try {
    if (!sock) {
      sendWml(
        res,
        resultCard("Error", ["Not connected to WhatsApp"], "/wml/me.wml")
      );
      return;
    }

    const user = sock.user;
    let currentStatus = "Loading...";

    try {
      const status = await sock.fetchStatus(user.id);
      currentStatus = status?.status || "No status set";
    } catch (e) {
      currentStatus = "Could not load status";
    }

    const success = req.query.success === "1";
    const preset = req.query.preset || "";

    const successMessage = success
      ? `
      <p><b>✓ Status Updated Successfully!</b></p>
      <p></p>
    `
      : "";

    const statusTemplates = [
      "Available",
      "Busy",
      "At work",
      "Can't talk, WhatsApp only",
      "In a meeting",
      "Sleeping",
      "Battery about to die",
    ];

    const body = `
      <p><b>Edit Status Message</b></p>
      ${successMessage}
      
      <p>Current Status: <b>${esc(currentStatus)}</b></p>
      
      <p>New Status:</p>
      <input name="status" title="Status message" value="${esc(
        preset ||
          (currentStatus !== "Loading..." &&
          currentStatus !== "Could not load status"
            ? currentStatus
            : "")
      )}" size="30" maxlength="139"/>
      
      <p><small>Max 139 characters. Leave empty to remove status.</small></p>
      
      <p>
        <anchor title="Update">Update
          <go method="post" href="/wml/profile.update-status">
            <postfield name="status" value="$(status)"/>
          </go>
        </anchor>
      </p>
      <do type="accept" label="${t('common.update')}">
        <go method="post" href="/wml/profile.update-status">
          <postfield name="status" value="$(status)"/>
        </go>
      </do>

      <p><b>Quick Status:</b></p>
      ${statusTemplates
        .map(
          (tmpl, i) =>
            `<p><a href="/wml/profile.edit-status.wml?preset=${encodeURIComponent(
              tmpl
            )}" accesskey="${i + 1}">[${i + 1}] ${esc(tmpl)}</a></p>`
        )
        .join("")}
      
      <p>
        <a href="/wml/me.wml" accesskey="0">[0] Back to Profile</a> |
        <a href="/wml/home.wml" accesskey="*">[*] Home</a>
      </p>
      
      <do type="options" label="${t('common.cancel')}">
        <go href="/wml/me.wml"/>
      </do>
    `;

    sendWml(res, card("edit-status", "Edit Status", body));
  } catch (e) {
    sendWml(
      res,
      resultCard(
        "Error",
        [e.message || "Failed to load status editor"],
        "/wml/me.wml"
      )
    );
  }
});

// View Profile Picture page (RIUSA SISTEMA MEDIA MESSAGGI - FIXED XML)
app.get("/wml/profile.picture.wml", async (req, res) => {
  try {
    if (!sock) {
      sendWml(
        res,
        resultCard("Error", ["Not connected to WhatsApp"], "/wml/me.wml")
      );
      return;
    }

    const user = sock.user;
    let profilePic = null;
    let hasProfilePic = false;

    try {
      profilePic = await sock.profilePictureUrl(user.id, "image");
      hasProfilePic = !!profilePic;
    } catch (e) {
      // No profile picture or error loading
    }

    const body = hasProfilePic
      ? `
      <p><b>My Profile Picture</b></p>
      <p>Profile picture available</p>
      
      <p><b>Nokia Compatible:</b></p>
      <p>
        <a href="/wml/view-profile-wbmp.wml" accesskey="1">[1] WBMP View</a><br/>
        <a href="/api/profile-picture/small.jpg" accesskey="2">[2] Small JPG</a><br/>
        <a href="/api/profile-picture/small.png" accesskey="3">[3] Small PNG</a><br/>
      </p>
      
      <p><b>Full Quality:</b></p>
      <p>
        <a href="${esc(profilePic)}" accesskey="4">[4] Original</a><br/>
        <a href="/api/profile-picture/jpg" accesskey="5">[5] Download JPG</a><br/>
        <a href="/api/profile-picture/png" accesskey="6">[6] Download PNG</a><br/>
      </p>
      
      <p><b>Mobile Formats:</b></p>
      <p>
        <a href="/api/profile-picture/wbmp" accesskey="7">[7] WBMP Download</a><br/>
        <a href="/api/profile-picture/thumbnail" accesskey="8">[8] Thumbnail</a><br/>
      </p>
    `
      : `
      <p><b>My Profile Picture</b></p>
      <p><em>No profile picture set</em></p>
      
      <p><b>Info:</b></p>
      <p>Profile picture can only be updated from WhatsApp mobile app.</p>
      <p>Once set, you can view it here in multiple formats including WBMP for old devices.</p>
    `;

    const fullBody = `
      ${body}
      
      <p>
        <a href="/wml/me.wml" accesskey="0">[0] Back to Profile</a> |
        <a href="/wml/home.wml" accesskey="*">[*] Home</a>
      </p>
      
      <do type="accept" label="${t('common.back')}">
        <go href="/wml/me.wml"/>
      </do>
      <do type="options" label="${t('common.refresh')}">
        <go href="/wml/profile.picture.wml"/>
      </do>
    `;

    sendWml(res, card("profile-pic", "Profile Picture", fullBody));
  } catch (e) {
    sendWml(
      res,
      resultCard(
        "Error",
        [e.message || "Failed to load profile picture"],
        "/wml/me.wml"
      )
    );
  }
});

// Pagina dedicata per visualizzare profile picture in WBMP (FIXED XML + HIGH FIDELITY)
app.get("/wml/view-profile-wbmp.wml", async (req, res) => {
  try {
    if (!sock) {
      sendWml(
        res,
        resultCard("Error", ["Not connected to WhatsApp"], "/wml/me.wml")
      );
      return;
    }

    const user = sock.user;
    let hasProfilePic = false;

    try {
      const profilePic = await sock.profilePictureUrl(user.id, "image");
      hasProfilePic = !!profilePic;
    } catch (e) {
      // No profile picture
    }

    // Escape sicuro per WML
    // Uses global escWml — single-pass O(L) instead of O(5L)

    let body = "";
    let title = "Profile Picture (WBMP)";

    if (hasProfilePic) {
      body = `<p><b>My Profile Picture</b></p>
<p>Nokia 7210 Compatible Format</p>
<p>
<img src="/api/profile-picture/wbmp" alt="Profile WBMP"/>
</p>
<p>
<a href="/wml/profile.picture.wml" accesskey="0">[0] Back to Picture Options</a>
</p>
<p>
<a href="/wml/me.wml" accesskey="1">[1] Back to Profile</a> |
<a href="/wml/home.wml" accesskey="9">[9] Home</a>
</p>`;
    } else {
      body = `<p><b>No Profile Picture</b></p>
<p>No profile picture set</p>
<p>
<a href="/wml/me.wml" accesskey="0">[0] Back to Profile</a>
</p>`;
    }

    const wmlOutput = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
<head><meta http-equiv="Cache-Control" content="no-cache, no-store"/></head>
<card id="wbmp-profile" title="${escWml(title)}">
${body}
<do type="accept" label="${t('common.back')}">
<go href="/wml/profile.picture.wml"/>
</do>
<do type="options" label="${t('home.profile')}">
<go href="/wml/me.wml"/>
</do>
</card>
</wml>`;

    sendRawWmlAware(res, wmlOutput);
  } catch (error) {
    logger.error("Profile WBMP view error:", error);
    res.status(500).send("Error loading profile WBMP view");
  }
});

// POST handler for updating name
app.post("/wml/profile.update-name", async (req, res) => {
  try {
    const { name } = req.body;
    if (!sock) throw new Error("Not connected");
    if (!name || name.trim().length === 0)
      throw new Error("Name cannot be empty");
    if (name.trim().length > 25)
      throw new Error("Name too long (max 25 characters)");

    await sock.updateProfileName(name.trim());

    sendWml(
      res,
      resultCard(
        "Name Updated",
        [
          `New name: ${esc(name.trim())}`,
          "Profile name updated successfully!",
          "Changes may take a few minutes to appear.",
        ],
        "/wml/profile.edit-name.wml?success=1",
        true
      )
    );
  } catch (e) {
    sendWml(
      res,
      resultCard(
        "Update Failed",
        [
          e.message || "Failed to update name",
          "Please try again or check connection",
        ],
        "/wml/profile.edit-name.wml"
      )
    );
  }
});

// POST handler for updating status
app.post("/wml/profile.update-status", async (req, res) => {
  try {
    const { status } = req.body;
    if (!sock) throw new Error("Not connected");
    if (status && status.length > 139)
      throw new Error("Status too long (max 139 characters)");

    await sock.updateProfileStatus(status || "");

    const statusText = status ? `"${status}"` : "Status cleared";

    sendWml(
      res,
      resultCard(
        "Status Updated",
        [
          `New status: ${esc(statusText)}`,
          "Status message updated successfully!",
          "Changes may take a few minutes to appear.",
        ],
        "/wml/profile.edit-status.wml?success=1",
        true
      )
    );
  } catch (e) {
    sendWml(
      res,
      resultCard(
        "Update Failed",
        [
          e.message || "Failed to update status",
          "Please try again or check connection",
        ],
        "/wml/profile.edit-status.wml"
      )
    );
  }
});

// API endpoint per servire profile picture in tutti i formati (come sistema media messaggi)

// Update profile picture endpoint
app.get("/api/profile-picture/:format", async (req, res) => {
  try {
    const { format } = req.params;
    if (!sock) return res.status(500).json({ error: "Not connected" });

    // Try to get profile picture - now handles LIDs
    let profilePicUrl;
    try {
      profilePicUrl = await sock.profilePictureUrl(sock.user.id, "image");
    } catch (e) {
      // Fallback to preview
      try {
        profilePicUrl = await sock.profilePictureUrl(sock.user.id, "preview");
      } catch (e2) {
        return res.status(404).json({ error: "No profile picture set" });
      }
    }

    if (!profilePicUrl) {
      return res.status(404).json({ error: "No profile picture set" });
    }

    // Download original image — O(1) network fetch
    const response = await axios.get(profilePicUrl, {
      responseType: "arraybuffer",
    });
    let mediaData = Buffer.from(response.data);

    // O(1) format lookup
    const formatMap = {
      'jpg': { mime: 'image/jpeg', ext: 'jpg' },
      'jpeg': { mime: 'image/jpeg', ext: 'jpg' },
      'png': { mime: 'image/png', ext: 'png' },
      'wbmp': { mime: 'image/vnd.wap.wbmp', ext: 'wbmp' },
      'thumbnail': { mime: 'image/jpeg', ext: 'jpg' },
      'small.jpg': { mime: 'image/jpeg', ext: 'jpg' },
      'small.png': { mime: 'image/png', ext: 'png' },
    };

    const fmt = formatMap[format];
    if (!fmt) {
      return res.status(400).json({ error: `Unsupported format: ${format}` });
    }

    // Convert based on requested format
    if (format === 'wbmp') {
      // Convert to WBMP for WAP 1.0 devices
      const targetWidth = 96;
      const { data: pixels, info } = await sharp(mediaData)
        .resize(targetWidth, targetWidth, { fit: 'cover', kernel: sharp.kernel.lanczos3 })
        .greyscale()
        .raw()
        .toBuffer({ resolveWithObject: true });

      mediaData = createWBMP(pixels, info.width, info.height);
    } else if (format === 'thumbnail' || format === 'small.jpg') {
      // Small JPEG for low-bandwidth devices
      mediaData = await sharp(mediaData)
        .resize(96, 96, { fit: 'cover' })
        .jpeg({ quality: 40 })
        .toBuffer();
    } else if (format === 'small.png') {
      mediaData = await sharp(mediaData)
        .resize(96, 96, { fit: 'cover' })
        .png({ compressionLevel: 9 })
        .toBuffer();
    } else if (format === 'jpg' || format === 'jpeg') {
      mediaData = await sharp(mediaData)
        .jpeg({ quality: 80 })
        .toBuffer();
    } else if (format === 'png') {
      mediaData = await sharp(mediaData)
        .png()
        .toBuffer();
    }

    res.setHeader("Content-Type", fmt.mime);
    res.setHeader("Content-Length", mediaData.length);
    res.setHeader("Cache-Control", "public, max-age=300");
    res.send(mediaData);
  } catch (error) {
    logger.error("Profile picture download error:", error);
    res.status(500).json({ error: error.message });
  }
});

// Presence page - was referenced but not implemented
app.get("/wml/presence.wml", (req, res) => {
  if (!sock) {
    sendWml(
      res,
      resultCard("Error", ["Not connected to WhatsApp"], "/wml/home.wml")
    );
    return;
  }

  const body = `
    <p><b>Update Presence</b></p>
    <p>Set your availability status:</p>
    
    <p><b>Global Presence:</b></p>
    <p>
      <a href="/wml/presence.set.wml?type=available" accesskey="1">[1] Available</a><br/>
      <a href="/wml/presence.set.wml?type=unavailable" accesskey="2">[2] Unavailable</a><br/>
      <a href="/wml/presence.set.wml?type=composing" accesskey="3">[3] Typing</a><br/>
      <a href="/wml/presence.set.wml?type=recording" accesskey="4">[4] Recording</a><br/>
      <a href="/wml/presence.set.wml?type=paused" accesskey="5">[5] Paused</a><br/>
    </p>
    
    <p><b>Chat-Specific:</b></p>
    <p>Contact/Group JID:</p>
    <input name="jid" title="JID" size="20"/>
    
    <p>Presence type:</p>
    <select name="presence" title="Presence">
      <option value="available">Available</option>
      <option value="unavailable">Unavailable</option>
      <option value="composing">Typing</option>
      <option value="recording">Recording</option>
      <option value="paused">Paused</option>
    </select>
    
    <p>
      <anchor title="Set">Set
        <go method="post" href="/wml/presence.set">
          <postfield name="jid" value="$(jid)"/>
          <postfield name="presence" value="$(presence)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.save')}">
      <go method="post" href="/wml/presence.set">
        <postfield name="jid" value="$(jid)"/>
        <postfield name="presence" value="$(presence)"/>
      </go>
    </do>

    ${navigationBar()}
  `;

  sendWml(res, card("presence", "Presence", body));
});

// Privacy page - was referenced but not implemented
app.get("/wml/privacy.wml", async (req, res) => {
  try {
    if (!sock) {
      sendWml(
        res,
        resultCard("Error", ["Not connected to WhatsApp"], "/wml/home.wml")
      );
      return;
    }

    let privacySettings = null;
    try {
      privacySettings = await sock.fetchPrivacySettings();
    } catch (e) {
      // Silent fail
    }

    const body = `
    
      <p><b>Privacy Settings</b></p>
      
      ${
        privacySettings
          ? `
      <p><b>Current Settings:</b></p>
      <p>Last Seen: ${esc(privacySettings.lastSeen || "Unknown")}</p>
      <p>Profile Photo: ${esc(privacySettings.profilePicture || "Unknown")}</p>
      <p>Status: ${esc(privacySettings.status || "Unknown")}</p>
      <p>Read Receipts: ${esc(privacySettings.readReceipts || "Unknown")}</p>
      `
          : "<p><em>Privacy settings unavailable</em></p>"
      }
      
      <p><b>Privacy Actions:</b></p>
      <p>
        <a href="/wml/privacy.lastseen.wml" accesskey="1">[1] Last Seen</a><br/>
        <a href="/wml/privacy.profile.wml" accesskey="2">[2] Profile Photo</a><br/>
        <a href="/wml/privacy.status.wml" accesskey="3">[3] Status Privacy</a><br/>
        <a href="/wml/privacy.receipts.wml" accesskey="4">[4] Read Receipts</a><br/>
        <a href="/wml/privacy.groups.wml" accesskey="5">[5] Groups</a><br/>
      </p>
      
      <p><b>${t('privacy.blocked_header')}</b></p>
      <p>
        <a href="/wml/blocked.list.wml" accesskey="7">${t('privacy.view_blocked')}</a><br/>
        <a href="/wml/block.contact.wml" accesskey="8">${t('privacy.block_contact')}</a><br/>
      </p>
      
      ${navigationBar()}
      
      <do type="accept" label="${t('common.refresh')}">
        <go href="/wml/privacy.wml"/>
      </do>
    `;

    sendWml(res, card("privacy", t('privacy.title'), body));
  } catch (e) {
    sendWml(
      res,
      resultCard(
        "Error",
        [e.message || "Failed to load privacy settings"],
        "/wml/home.wml"
      )
    );
  }
});

// =================== PRIVACY SUB-PAGES ===================

app.get("/wml/blocked.list.wml", async (req, res) => {
  try {
    if (!sock) {
      return sendWml(res, resultCard(t('common.error'), [t('privacy.not_connected')], "/wml/privacy.wml"));
    }
    const blocklist = await sock.fetchBlocklist();
    const page = parseInt(req.query.page || "1", 10);
    const pageSize = 5;
    const totalPages = Math.max(1, Math.ceil((blocklist.length || 0) / pageSize));
    const pageItems = (blocklist || []).slice((page - 1) * pageSize, page * pageSize);
    const listHtml = pageItems.length
      ? pageItems.map(jid =>
          `<p>${esc(jidFriendly(jid))} <a href="/wml/unblock.wml?jid=${encodeURIComponent(jid)}" accesskey="*">${t('common.unblock')}</a></p>`
        ).join("")
      : `<p><em>${t('privacy.no_blocked')}</em></p>`;
    const prevLink = page > 1 ? `<a href="/wml/blocked.list.wml?page=${page - 1}" accesskey="7">${t('common.prev')}</a> ` : "";
    const nextLink = page < totalPages ? `<a href="/wml/blocked.list.wml?page=${page + 1}" accesskey="8">${t('common.next')}</a>` : "";
    const body = `
      <p><b>${t('privacy.blocked_header')} (${blocklist.length || 0})</b></p>
      ${listHtml}
      ${(prevLink || nextLink) ? `<p>${prevLink}${nextLink}</p>` : ""}
      <p><a href="/wml/block.contact.wml" accesskey="1">${t('privacy.block_new')}</a></p>
      <p><a href="/wml/privacy.wml" accesskey="0">${t('common.back')}</a></p>
      <do type="accept" label="${t('common.refresh')}">
        <go href="/wml/blocked.list.wml"/>
      </do>
    `;
    sendWml(res, card("blocked-list", t('privacy.blocked_header'), body));
  } catch (e) {
    sendWml(res, resultCard(t('common.error'), [e.message || t('privacy.load_failed')], "/wml/privacy.wml"));
  }
});

app.get("/wml/block.contact.wml", (req, res) => {
  const body = `
    <p><b>Block a Contact</b></p>
    <p>Enter phone number to block:</p>
    <input name="phone" title="Phone number" size="20" maxlength="30"/>
    <p>
      <anchor title="Block">Block
        <go method="post" href="/wml/block.contact">
          <postfield name="phone" value="$(phone)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.block')}">
      <go method="post" href="/wml/block.contact">
        <postfield name="phone" value="$(phone)"/>
      </go>
    </do>
    <p><a href="/wml/blocked.list.wml" accesskey="0">[0] Cancel</a></p>
  `;
  sendWml(res, card("block-contact", "Block Contact", body));
});

app.post("/wml/block.contact", async (req, res) => {
  const { phone } = req.body;
  try {
    if (!sock) throw new Error("Not connected");
    const jid = formatJid(phone);
    await sock.updateBlockStatus(jid, "block");
    sendWml(res, resultCard("Blocked", [`${jidFriendly(jid)} has been blocked`], "/wml/blocked.list.wml"));
  } catch (e) {
    sendWml(res, resultCard("Error", [e.message || "Block failed"], "/wml/block.contact.wml"));
  }
});

app.get("/wml/privacy.receipts.wml", async (req, res) => {
  try {
    if (!sock) {
      return sendWml(res, resultCard("Error", ["Not connected"], "/wml/privacy.wml"));
    }
    let current = "unknown";
    try {
      const privacy = await sock.fetchPrivacySettings();
      current = privacy.readReceipts || "all";
    } catch (e) { /* silent */ }
    const body = `
      <p><b>Read Receipts</b></p>
      <p>Current: ${esc(current)}</p>
      <p><small>Note: Disabling hides your read status from others but you won't see theirs either.</small></p>
      <p>Set read receipts:</p>
      <select name="value" title="Read Receipts">
        <option value="all">Everyone (on)</option>
        <option value="none">Nobody (off)</option>
      </select>
      <p>
        <anchor title="Save">Save
          <go method="post" href="/wml/privacy.receipts">
            <postfield name="value" value="$(value)"/>
          </go>
        </anchor>
      </p>
      <do type="accept" label="${t('common.save')}">
        <go method="post" href="/wml/privacy.receipts">
          <postfield name="value" value="$(value)"/>
        </go>
      </do>
      <p><a href="/wml/privacy.wml" accesskey="0">[0] Back</a></p>
    `;
    sendWml(res, card("privacy-receipts", "Read Receipts", body));
  } catch (e) {
    sendWml(res, resultCard("Error", [e.message || "Failed"], "/wml/privacy.wml"));
  }
});

app.post("/wml/privacy.receipts", async (req, res) => {
  const { value } = req.body;
  try {
    if (!sock) throw new Error("Not connected");
    await sock.updatePrivacySettings({ readReceipts: value });
    sendWml(res, resultCard("Saved", [`Read receipts set to: ${esc(value)}`], "/wml/privacy.wml"));
  } catch (e) {
    sendWml(res, resultCard("Error", [e.message || "Update failed"], "/wml/privacy.receipts.wml"));
  }
});

app.get("/wml/privacy.groups.wml", async (req, res) => {
  try {
    if (!sock) {
      return sendWml(res, resultCard("Error", ["Not connected"], "/wml/privacy.wml"));
    }
    let current = "all";
    try {
      const privacy = await sock.fetchPrivacySettings();
      current = privacy.groupadd || "all";
    } catch (e) { /* silent */ }
    const body = `
      <p><b>Who Can Add You to Groups</b></p>
      <p>Current: ${esc(current)}</p>
      <p>Choose setting:</p>
      <select name="value" title="Group Add Privacy">
        <option value="all">Everyone</option>
        <option value="contacts">My Contacts</option>
        <option value="contact_blacklist">My Contacts Except</option>
        <option value="none">Nobody</option>
      </select>
      <p>
        <anchor title="Save">Save
          <go method="post" href="/wml/privacy.groups">
            <postfield name="value" value="$(value)"/>
          </go>
        </anchor>
      </p>
      <do type="accept" label="${t('common.save')}">
        <go method="post" href="/wml/privacy.groups">
          <postfield name="value" value="$(value)"/>
        </go>
      </do>
      <p><a href="/wml/privacy.wml" accesskey="0">[0] Back</a></p>
    `;
    sendWml(res, card("privacy-groups", "Groups Privacy", body));
  } catch (e) {
    sendWml(res, resultCard("Error", [e.message || "Failed"], "/wml/privacy.wml"));
  }
});

app.post("/wml/privacy.groups", async (req, res) => {
  const { value } = req.body;
  try {
    if (!sock) throw new Error("Not connected");
    await sock.updatePrivacySettings({ groupadd: value });
    sendWml(res, resultCard("Saved", [`Groups privacy set to: ${esc(value)}`], "/wml/privacy.wml"));
  } catch (e) {
    sendWml(res, resultCard("Error", [e.message || "Update failed"], "/wml/privacy.groups.wml"));
  }
});

// =================== POST HANDLERS FOR QUICK ACTIONS ===================

// Presence setting handler
app.post("/wml/presence.set", async (req, res) => {
  try {
    const { jid, presence = "available" } = req.body;
    const type = req.query.type || presence;

    if (!sock) {
      sendWml(
        res,
        resultCard("Error", ["Not connected to WhatsApp"], "/wml/presence.wml")
      );
      return;
    }

    if (jid && jid.trim()) {
      await sock.sendPresenceUpdate(type, formatJid(jid.trim()));
      sendWml(
        res,
        resultCard(
          "Presence Updated",
          [
            `Set ${type} for ${esc(jid.trim())}`,
            "Presence updated successfully",
          ],
          "/wml/presence.wml",
          true
        )
      );
    } else {
      await sock.sendPresenceUpdate(type);
      sendWml(
        res,
        resultCard(
          "Presence Updated",
          [`Global presence set to ${type}`, "Presence updated successfully"],
          "/wml/presence.wml",
          true
        )
      );
    }
  } catch (e) {
    sendWml(
      res,
      resultCard(
        "Presence Failed",
        [e.message || "Failed to update presence"],
        "/wml/presence.wml"
      )
    );
  }
});

// Quick presence setting via GET for simple links
app.get("/wml/presence.set.wml", async (req, res) => {
  try {
    const { type = "available", jid } = req.query;

    if (!sock) {
      sendWml(
        res,
        resultCard("Error", ["Not connected to WhatsApp"], "/wml/presence.wml")
      );
      return;
    }

    if (jid && jid.trim()) {
      await sock.sendPresenceUpdate(type, formatJid(jid.trim()));
      sendWml(
        res,
        resultCard(
          "Presence Updated",
          [
            `Set ${type} for ${esc(jid.trim())}`,
            "Presence updated successfully",
          ],
          "/wml/presence.wml",
          true
        )
      );
    } else {
      await sock.sendPresenceUpdate(type);
      sendWml(
        res,
        resultCard(
          "Global Presence Updated",
          [`Presence set to: ${type}`, "All contacts will see this status"],
          "/wml/presence.wml",
          true
        )
      );
    }
  } catch (e) {
    sendWml(
      res,
      resultCard(
        "Presence Failed",
        [e.message || "Failed to update presence"],
        "/wml/presence.wml"
      )
    );
  }
});

// =================== MISSING UTILITY ENDPOINTS ===================

// Broadcast page - was referenced but missing
app.get("/wml/broadcast.wml", (req, res) => {
  const body = `
    <p><b>Broadcast Message</b></p>
    <p>Send message to multiple contacts</p>
    
    <p>Recipients (comma-separated):</p>
    <input name="recipients" title="Phone numbers" size="25" maxlength="500"/>
    
    <p>Message:</p>
    <input name="message" title="Your message" size="30" maxlength="1000"/>
    
    <p>Delay between sends (ms):</p>
    <select name="delay" title="Delay">
      <option value="1000">1 second</option>
      <option value="2000">2 seconds</option>
      <option value="5000">5 seconds</option>
      <option value="10000">10 seconds</option>
    </select>
    
    <p>
      <anchor title="Send">Send
        <go method="post" href="/wml/broadcast.send">
          <postfield name="recipients" value="$(recipients)"/>
          <postfield name="message" value="$(message)"/>
          <postfield name="delay" value="$(delay)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.send')}">
      <go method="post" href="/wml/broadcast.send">
        <postfield name="recipients" value="$(recipients)"/>
        <postfield name="message" value="$(message)"/>
        <postfield name="delay" value="$(delay)"/>
      </go>
    </do>

    <p>
      <a href="/wml/contacts.wml" accesskey="1">[1] Select from Contacts</a> |
      <a href="/wml/home.wml" accesskey="0">[0] Home</a>
    </p>
  `;

  sendWml(res, card("broadcast", "Broadcast", body));
});

app.post("/wml/broadcast.send", async (req, res) => {
  const { recipients, message, delay: delayMs } = req.body;
  try {
    if (!sock) throw new Error("Not connected");
    if (!recipients || !message) throw new Error("Recipients and message are required");
    const phones = recipients.split(",")
      .map(p => p.trim())
      .filter(p => /^[0-9\-\+\*#\(\)]+$/.test(p))
      .slice(0, 100); // Cap at 100 recipients
    if (phones.length === 0) throw new Error("No valid recipients");
    const waitMs = Math.max(1000, Math.min(10000, parseInt(delayMs, 10) || 2000));
    const results = [];
    for (const phone of phones) {
      try {
        await sock.sendMessage(formatJid(phone), { text: message });
        results.push(`OK: ${jidFriendly(phone)}`);
      } catch (e) {
        results.push(`FAIL: ${jidFriendly(phone)}`);
      }
      if (phones.indexOf(phone) < phones.length - 1) {
        await new Promise(r => setTimeout(r, waitMs));
      }
    }
    const summary = `Sent to ${results.filter(r => r.startsWith("OK")).length}/${phones.length}`;
    sendWml(res, resultCard("Broadcast Done", [summary, ...results.slice(0, 5)], "/wml/broadcast.wml"));
  } catch (e) {
    sendWml(res, resultCard("Error", [e.message || "Broadcast failed"], "/wml/broadcast.wml"));
  }
});

// Debug page - was referenced but missing
app.get("/wml/debug.wml", (req, res) => {
  const memUsage = process.memoryUsage();
  const uptime = Math.floor(process.uptime());

  const body = `

    <p><b>Debug Information</b></p>
    
    <p><b>Connection:</b></p>
    <p>State: ${esc(connectionState)}</p>
    <p>Socket: ${sock ? "Active" : "Null"}</p>
    <p>User: ${sock?.user?.id ? esc(sock.user.id) : "None"}</p>
    <p>QR: ${currentQR ? "Available" : "None"}</p>
    
    <p><b>Data Stores:</b></p>
    <p>Contacts: ${contactStore.size}</p>
    <p>Chats: ${chatStore.size}</p>
    <p>Messages: ${messageStore.size}</p>
    <p>Sync Status: ${isFullySynced ? "Complete" : "Pending"}</p>
    <p>Sync Attempts: ${syncAttempts}</p>
    
    <p><b>System:</b></p>
    <p>Uptime: ${uptime}s</p>
    <p>Memory: ${Math.round(memUsage.rss / 1024 / 1024)}MB</p>
    <p>Node: ${process.version}</p>
    <p>Env: ${NODE_ENV}</p>
    
    <p><b>Debug Actions:</b></p>
    <p>
      <a href="/wml/debug.stores.wml" accesskey="1">[1] Store Details</a><br/>
      <a href="/wml/debug.logs.wml" accesskey="2">[2] Recent Logs</a><br/>
      <a href="/wml/debug.test.wml" accesskey="3">[3] Connection Test</a><br/>
    </p>
    
    ${navigationBar()}
    
    <do type="accept" label="${t('common.refresh')}">
      <go href="/wml/debug.wml"/>
    </do>
  `;

  sendWml(res, card("debug", "Debug", body, "/wml/debug.wml"));
});

// =================== DEBUG SUB-PAGES ===================

app.get("/wml/debug.stores.wml", (req, res) => {
  const chatIds = Array.from(chatStore.keys()).slice(0, 10);
  const chatList = chatIds.map(cid => {
    const msgs = chatStore.get(cid) || [];
    return `<p>${esc(jidFriendly(cid))}: ${msgs.length} msgs</p>`;
  }).join("");
  const body = `
    <p><b>Store Details</b></p>
    <p><b>Contacts:</b> ${contactStore.size}</p>
    <p><b>Chats:</b> ${chatStore.size}</p>
    <p><b>Messages:</b> ${messageStore.size}</p>
    <p><b>Chat ID Sets:</b> ${chatMessageIdSets.size}</p>
    <p><b>Top Chats (by store):</b></p>
    ${chatList || "<p><em>No chats</em></p>"}
    ${chatStore.size > 10 ? `<p><small>...and ${chatStore.size - 10} more</small></p>` : ""}
    <p><a href="/wml/debug.wml" accesskey="0">[0] Back</a></p>
    <do type="accept" label="${t('common.refresh')}">
      <go href="/wml/debug.stores.wml"/>
    </do>
  `;
  sendWml(res, card("debug-stores", "Store Details", body));
});

app.get("/wml/debug.logs.wml", (req, res) => {
  const uptime = Math.floor(process.uptime());
  const mem = process.memoryUsage();
  const body = `
    <p><b>System Info</b></p>
    <p>Uptime: ${uptime}s</p>
    <p>RSS: ${Math.round(mem.rss / 1024 / 1024)}MB</p>
    <p>Heap Used: ${Math.round(mem.heapUsed / 1024 / 1024)}MB</p>
    <p>Heap Total: ${Math.round(mem.heapTotal / 1024 / 1024)}MB</p>
    <p><b>Connection:</b></p>
    <p>State: ${esc(connectionState)}</p>
    <p>Synced: ${isFullySynced ? "Yes" : "No"}</p>
    <p>Sync Attempts: ${syncAttempts}</p>
    <p><b>Auth:</b></p>
    <p>Creds: ${sock?.authState?.creds ? "Present" : "Missing"}</p>
    <p>User: ${sock?.user?.id ? esc(jidFriendly(sock.user.id)) : "None"}</p>
    <p><a href="/wml/debug.wml" accesskey="0">[0] Back</a></p>
    <do type="accept" label="${t('common.refresh')}">
      <go href="/wml/debug.logs.wml"/>
    </do>
  `;
  sendWml(res, card("debug-logs", "System Info", body));
});

app.get("/wml/debug.test.wml", async (req, res) => {
  const tests = [];
  tests.push(`Socket: ${sock ? "OK" : "MISSING"}`);
  tests.push(`Connection: ${connectionState}`);
  tests.push(`Auth Creds: ${sock?.authState?.creds ? "OK" : "MISSING"}`);
  tests.push(`Contacts: ${contactStore.size}`);
  tests.push(`Chats: ${chatStore.size}`);
  tests.push(`Messages: ${messageStore.size}`);
  tests.push(`Fully Synced: ${isFullySynced}`);
  const testItems = tests.map(t => `<p>${esc(t)}</p>`).join("");
  const body = `
    <p><b>Connection Test</b></p>
    ${testItems}
    <p><a href="/wml/debug.wml" accesskey="0">[0] Back</a></p>
    <do type="accept" label="${t('common.refresh')}">
      <go href="/wml/debug.test.wml"/>
    </do>
  `;
  sendWml(res, card("debug-test", "Connection Test", body));
});

// =================== MENU PAGE ===================

app.get("/wml/menu.wml", (req, res) => {
  const body = `
    <p><b>Main Menu</b></p>
    <p>
      <a href="/wml/home.wml" accesskey="1">[1] Home</a><br/>
      <a href="/wml/chats.wml" accesskey="2">[2] Chats</a><br/>
      <a href="/wml/contacts.wml" accesskey="3">[3] Contacts</a><br/>
      <a href="/wml/send-menu.wml" accesskey="4">[4] New Message</a><br/>
      <a href="/wml/groups.wml" accesskey="5">[5] Groups</a><br/>
      <a href="/wml/broadcast.wml" accesskey="6">[6] Broadcast</a><br/>
      <a href="/wml/privacy.wml" accesskey="7">[7] Privacy</a><br/>
      <a href="/wml/settings.wml" accesskey="8">[8] Settings</a><br/>
      <a href="/wml/debug.wml" accesskey="9">[9] Debug</a><br/>
      <a href="/wml/logout.wml" accesskey="0">[0] Logout</a>
    </p>
    <do type="accept" label="${t('home.title')}">
      <go href="/wml/home.wml"/>
    </do>
  `;
  sendWml(res, card("menu", "Menu", body));
});

// Logout confirmation page
app.get("/wml/logout.wml", (req, res) => {
  const body = `
    <p><b>Logout Confirmation</b></p>
    <p>This will:</p>
    <p>• Disconnect from WhatsApp</p>
    <p>• Clear all session data</p>
    <p>• Remove authentication</p>
    <p>• Clear local contacts/chats</p>
    
    <p><b>Are you sure?</b></p>
    <p>
      <a href="/wml/logout.confirm.wml" accesskey="1">[1] Yes, Logout</a><br/>
      <a href="/wml/home.wml" accesskey="0">[0] Cancel</a><br/>
    </p>
    
    <do type="accept" label="${t('common.cancel')}">
      <go href="/wml/home.wml"/>
    </do>
  `;

  sendWml(res, card("logout", "Logout", body));
});

// Logout execution
app.get("/wml/logout.confirm.wml", async (req, res) => {
  try {
    // Save data IMMEDIATELY before logout
    logger.info("Saving all data before logout...");
    await storage.saveImmediately("contacts", contactStore);
    await storage.saveImmediately("chats", chatStore);
    await storage.saveImmediately("messages", messageStore);
    await storage.saveImmediately("meta", {
      isFullySynced,
      syncAttempts,
      lastSync: new Date().toISOString(),
      contactsCount: contactStore.size,
      chatsCount: chatStore.size,
      messagesCount: messageStore.size,
    });

    if (sock) {
      await sock.logout();
    }

    // Clear auth files
    if (fs.existsSync("./auth_info_baileys")) {
      fs.rmSync("./auth_info_baileys", { recursive: true });
    }

    // DO NOT clear stores - keep data persistent
    // contactStore.clear();
    // chatStore.clear();
    // messageStore.clear();
    isFullySynced = false;
    syncAttempts = 0;
    currentQR = null;
    currentPairingCode = null;
    connectionState = "disconnected";

    // Revoke URL auth token and destroy session so WAP 1.x and 2.x are both logged out
    req.session.destroy(() => {
      sendWml(
        res,
        resultCard(
          "Logged Out",
          [
            "Successfully logged out",
            "You can scan QR to reconnect",
          ],
          "/login",
          false
        )
      );
    });
  } catch (e) {
    sendWml(
      res,
      resultCard(
        "Logout Error",
        [e.message || "Logout failed"],
        "/wml/home.wml"
      )
    );
  }
});

// =================== SYNC ENDPOINTS ===================

// Force sync endpoints that were referenced but missing handlers
app.get("/wml/sync.full.wml", async (req, res) => {
  try {
    if (!sock) {
      sendWml(
        res,
        resultCard("Error", ["Not connected to WhatsApp"], "/wml/status.wml")
      );
      return;
    }

    // Trigger the existing performInitialSync function
    performInitialSync();

    sendWml(
      res,
      resultCard(
        "Sync Started",
        [
          "Full sync initiated",
          "This may take a few minutes",
          "Check status page for progress",
        ],
        "/wml/status.wml",
        true
      )
    );
  } catch (e) {
    sendWml(
      res,
      resultCard(
        "Sync Failed",
        [e.message || "Failed to start sync"],
        "/wml/status.wml"
      )
    );
  }
});

app.get("/wml/sync.contacts.wml", async (req, res) => {
  try {
    if (!sock) {
      sendWml(
        res,
        resultCard("Error", ["Not connected to WhatsApp"], "/wml/status.wml")
      );
      return;
    }

    const initialCount = contactStore.size;

    // Wait for contact events (contacts sync automatically in Baileys)
    await delay(3000);

    const finalCount = contactStore.size;
    const newContacts = finalCount - initialCount;

    sendWml(
      res,
      resultCard(
        "Contact Sync Complete",
        [
          `Initial contacts: ${initialCount}`,
          `Final contacts: ${finalCount}`,
          `New contacts: ${newContacts}`,
          "Contacts sync via WhatsApp events",
        ],
        "/wml/status.wml",
        true
      )
    );
  } catch (e) {
    sendWml(
      res,
      resultCard(
        "Contact Sync Failed",
        [e.message || "Failed to sync contacts"],
        "/wml/status.wml"
      )
    );
  }
});

// Enhanced Chats page with search and pagination
app.get("/wml/chats.wml", async (req, res) => {
  const userAgent = req.headers["user-agent"] || "";

  // Use req.query for GET requests, like in contacts
  const query = req.query;

  const page = Math.max(1, parseInt(query.page || "1"));
  let limit = 3; // Fisso a 3 elementi per pagina

  // More restrictive limits for WAP 1.0 devices (like contacts)
  if (userAgent.includes("Nokia") || userAgent.includes("UP.Browser")) {
    limit = Math.min(3, limit); // Max 3 items per page
  }
  limit = Math.min(3, limit); // Max 3 items per page
  const search = query.q || "";
  const refreshNonce = Date.now();
  const showGroups = query.groups !== "0"; // Default show groups
  const showDirect = query.direct !== "0"; // Default show direct chats

  // Auto-sync if no chats and not synced yet
  if (chatStore.size === 0 && !isFullySynced && sock) {
    try {
      logger.info("💬 No chats found, attempting auto-sync...");
      const groups = await sock.groupFetchAllParticipating();

      Object.keys(groups).forEach((chatId) => {
        if (!chatStore.has(chatId)) {
          chatStore.set(chatId, []);
        }
      });

      logger.info(`💬 Auto-synced ${Object.keys(groups).length} group chats`);
      await delay(1000); // Brief wait for additional events
    } catch (syncError) {
      logger.warn("⚠️ Auto-sync failed:", syncError.message);
    }
  }

  // Single-pass build + filter inline (avoids 3 separate O(C) filter passes + O(C) Array.from)
  const searchLower = search ? search.toLowerCase() : '';
  let chats = [];
  for (const chatId of chatStore.keys()) {
    const isGroup = chatId.endsWith("@g.us");

    // Type filter — skip early before building object
    if (!showGroups && isGroup) continue;
    if (!showDirect && !isGroup) continue;

    const messages = chatStore.get(chatId) || [];
    const lastMessage = messages.length > 0 ? messages[messages.length - 1] : null;
    const phoneNumber = chatId.replace("@s.whatsapp.net", "").replace("@g.us", "");

    const contact = contactStore.get(chatId) || {};
    const chatName = contact.subject || contact.name || contact.notify || contact.verifiedName || jidFriendly(chatId);
    const lastMessageText = lastMessage ? messageText(lastMessage) : "No messages";

    // Search filter — skip early before building full object
    if (searchLower) {
      const nameMatch = chatName.toLowerCase().includes(searchLower);
      const numberMatch = phoneNumber && phoneNumber.includes(searchLower);
      const messageMatch = (lastMessageText || '').toLowerCase().includes(searchLower);
      if (!nameMatch && !numberMatch && !messageMatch) continue;
    }

    const lastTimestamp = lastMessage ? Number(lastMessage.messageTimestamp) : 0;

    chats.push({
      id: chatId,
      name: chatName,
      isGroup,
      phoneNumber: isGroup ? null : phoneNumber,
      messageCount: messages.length,
      lastMessage: {
        text: lastMessageText || "No message text",
        timestamp: lastTimestamp,
        fromMe: lastMessage ? lastMessage.key.fromMe : false,
        timeStr: lastTimestamp > 0
          ? new Date(lastTimestamp * 1000).toLocaleString("en-GB", { day: "2-digit", month: "short", year: "numeric", hour: "2-digit", minute: "2-digit", second: "2-digit" })
          : "Never",
      },
      unreadCount: 0,
      contact,
    });
  }

  // Sort by last message timestamp (most recent first)
  chats.sort((a, b) => b.lastMessage.timestamp - a.lastMessage.timestamp);

  const total = chats.length;
  const start = (page - 1) * limit;
  const items = chats.slice(start, start + limit);

  // Resolve accurate names + unread counts only for the visible page items (max 3 instead of ALL)
  await Promise.all(
    items.map(async (item) => {
      item.name = await getContactName(item.id, sock);
      // O(1) unreadCount via per-chat cache (was O(M) filter)
      item.unreadCount = getChatUnreadCount(item.id);
    })
  );

  // Safe WML escaping function (like contacts)
  // Uses global escWml — single-pass O(L) instead of O(5L)

  // Page header — compact: chat count + page info on one line
  const searchHeader = search
    ? `<p><b>${t('chat.searching')}</b> ${escWml(search)} (${total}) ${t('chats.page')} ${page}/${Math.ceil(total / limit) || 1}</p>`
    : `<p><b>${t('chats.title')}</b> ${total} | ${t('chats.page')} ${page}/${Math.ceil(total / limit) || 1}</p>`;

  // Chat list
  // In your chats.wml route, fix the list mapping section:

  const list =
    items
      .map((c, idx) => {
        const unreadBadge = c.unreadCount > 0 ? ` (${c.unreadCount})` : "";

        // Add safety checks for lastMessage properties
        const lastMessageText = c.lastMessage?.text || "No message text";
        const fromMe = c.lastMessage?.fromMe || false;

        // Safe text processing
        const messagePreview =
          lastMessageText.length > 40
            ? lastMessageText.substring(0, 37) + "..."
            : lastMessageText;
        const fromIndicator = fromMe ? "[out] " : "[in] ";

        // Safe time string access
        const timeStr = c.lastMessage?.timeStr || "Unknown time";

        const typeTag = c.isGroup ? "[G]" : "[D]";
        const shortName = c.name.length > 14 ? c.name.substring(0, 13) + "." : c.name;
        return `<p><b>${start + idx + 1}. ${escWml(shortName)}</b>${typeTag}${unreadBadge}<br/>
      <small>${escWml(fromIndicator + messagePreview)}</small><br/>
      <small>${escWml(timeStr)} (${c.messageCount})</small><br/>
      <a href="/wml/chat.wml?jid=${encodeURIComponent(c.id)}&amp;limit=3">[Open]</a>
      <a href="/wml/send.text.wml?to=${encodeURIComponent(c.id)}">[Send]</a>
      ${c.phoneNumber ? `<a href="wtai://wp/mc;${c.phoneNumber}">[Call]</a>` : ""}
    </p>`;
      })
      .join("") || "<p>No chats found.</p>";

  // Pagination con First/Last e numeri di pagina
  const totalPages = Math.ceil(total / limit) || 1;

  const firstPage =
    page > 1
      ? `<a href="/wml/chats.wml?page=1&amp;limit=${limit}&amp;q=${encodeURIComponent(
          search
        )}&amp;groups=${showGroups ? 1 : 0}&amp;direct=${
          showDirect ? 1 : 0
        }">[First]</a>`
      : "";

  const prevPage =
    page > 1
      ? `<a href="/wml/chats.wml?page=${
          page - 1
        }&amp;limit=${limit}&amp;q=${encodeURIComponent(search)}&amp;groups=${
          showGroups ? 1 : 0
        }&amp;direct=${showDirect ? 1 : 0}">[Previous]</a>`
      : "";

  const nextPage =
    page < totalPages
      ? `<a href="/wml/chats.wml?page=${
          page + 1
        }&amp;limit=${limit}&amp;q=${encodeURIComponent(search)}&amp;groups=${
          showGroups ? 1 : 0
        }&amp;direct=${showDirect ? 1 : 0}">[Next]</a>`
      : "";

  const lastPage =
    page < totalPages
      ? `<a href="/wml/chats.wml?page=${totalPages}&amp;limit=${limit}&amp;q=${encodeURIComponent(
          search
        )}&amp;groups=${showGroups ? 1 : 0}&amp;direct=${
          showDirect ? 1 : 0
        }">[Last]</a>`
      : "";

  // numeri di pagina (massimo 5 visibili: due prima, attuale, due dopo)
  let pageNumbers = "";
  const startPage = Math.max(1, page - 2);
  const endPage = Math.min(totalPages, page + 2);
  for (let p = startPage; p <= endPage; p++) {
    if (p === page) {
      pageNumbers += `<b>[${p}]</b> `;
    } else {
      pageNumbers += `<a href="/wml/chats.wml?page=${p}&amp;limit=${limit}&amp;q=${encodeURIComponent(
        search
      )}&amp;groups=${showGroups ? 1 : 0}&amp;direct=${
        showDirect ? 1 : 0
      }">${p}</a> `;
    }
  }

  const pagination = `
    <p>
      ${firstPage} ${firstPage && prevPage ? "" : ""} ${prevPage}
      ${pageNumbers}
      ${nextPage} ${nextPage && lastPage ? "" : ""} ${lastPage}
    </p>`;

  // Simplified search form (like contacts)
  const searchForm = `
    <p><b>${t('chats.search')}</b></p>
    <p>
      <input name="q" title="${t('chats.search_placeholder')}" value="${escWml(
        search
      )}" emptyok="true" size="15" maxlength="30"/>
    </p>
    <p>
      <anchor title="${t('chats.search_btn')}">${t('chats.search_btn')}
        <go href="/wml/chats.wml" method="get">
          <postfield name="q" value="$(q)"/>
          <postfield name="groups" value="$(groups)"/>
          <postfield name="direct" value="$(direct)"/>
          <postfield name="page" value="1"/>
          <postfield name="limit" value="${limit}"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('chats.search_btn')}">
      <go href="/wml/chats.wml" method="get">
        <postfield name="q" value="$(q)"/>
        <postfield name="groups" value="$(groups)"/>
        <postfield name="direct" value="$(direct)"/>
        <postfield name="page" value="1"/>
        <postfield name="limit" value="${limit}"/>
      </go>
    </do>`;

  // Filter toggles — compact single line
  const filterToggles = `
    <p>
      ${
        showGroups
          ? `<a href="/wml/chats.wml?page=${page}&amp;limit=${limit}&amp;q=${encodeURIComponent(search)}&amp;groups=0&amp;direct=${showDirect ? 1 : 0}">[G-off]</a>`
          : `<a href="/wml/chats.wml?page=${page}&amp;limit=${limit}&amp;q=${encodeURIComponent(search)}&amp;groups=1&amp;direct=${showDirect ? 1 : 0}">[G-on]</a>`
      }
      ${
        showDirect
          ? `<a href="/wml/chats.wml?page=${page}&amp;limit=${limit}&amp;q=${encodeURIComponent(search)}&amp;groups=${showGroups ? 1 : 0}&amp;direct=0">[D-off]</a>`
          : `<a href="/wml/chats.wml?page=${page}&amp;limit=${limit}&amp;q=${encodeURIComponent(search)}&amp;groups=${showGroups ? 1 : 0}&amp;direct=1">[D-on]</a>`
      }
    </p>`;

  // WML card body
  const body = `
    ${searchHeader}
    ${searchForm}
    ${filterToggles}
    ${list}
    ${pagination}
    <p>
      <a href="/wml/home.wml" accesskey="0">${t('chats.home')}</a>
      <a href="/wml/send-menu.wml" accesskey="4">${t('chats.new_msg')}</a>
    </p>
    <do type="accept" label="${t('chats.refresh')}">
      <go href="/wml/chats.wml?page=${page}&amp;limit=${limit}&amp;q=${encodeURIComponent(
    search
  )}&amp;groups=${showGroups ? 1 : 0}&amp;direct=${showDirect ? 1 : 0}&amp;_rt=${refreshNonce}"/>
    </do>
    <do type="options" label="${t('home.title')}">
      <go href="/wml/home.wml"/>
    </do>`;

  // Create complete WML string
  const wmlOutput = `<?xml version="1.0"?>
<!DOCTYPE wml PUBLIC "-//WAPFORUM//DTD WML 1.1//EN" "http://www.wapforum.org/DTD/wml_1.1.xml">
<wml>
  <head>
    <meta http-equiv="Cache-Control" content="no-cache, no-store"/>
  </head>
  <card id="chats" title="${t('chats.title')}" ontimer="/wml/chats.wml?_rt=${refreshNonce}">
    <onevent type="ontimer">
      <go href="/wml/chats.wml?_rt=${refreshNonce}"/>
    </onevent>
    <timer value="${getWmlRefreshTimerUnits()}"/>
    ${body}
  </card>
</wml>`;

  sendRawWmlAware(res, wmlOutput);
});

// Advanced chat search page
app.get("/wml/chats.search.wml", async (req, res) => {
  const prevQuery = esc(req.query.q || "");
  const prevType = req.query.type || "all";
  const prevSort = req.query.sort || "recent";

  const body = `
    <p><b>Advanced Chat Search</b></p>
    
    <p>Search query:</p>
    <input name="q" title="Search query" value="${prevQuery}" size="20" maxlength="100"/>
    
    <p>Chat type:</p>
    <select name="type" title="Chat Type">
      <option value="all" ${
        prevType === "all" ? 'selected="selected"' : ""
      }>All Chats</option>
      <option value="direct" ${
        prevType === "direct" ? 'selected="selected"' : ""
      }>Direct Messages</option>
      <option value="groups" ${
        prevType === "groups" ? 'selected="selected"' : ""
      }>Groups Only</option>
    </select>
    
    <p>Sort by:</p>
    <select name="sort" title="Sort Order">
      <option value="recent" ${
        prevSort === "recent" ? 'selected="selected"' : ""
      }>Most Recent</option>
      <option value="messages" ${
        prevSort === "messages" ? 'selected="selected"' : ""
      }>Most Messages</option>
      <option value="name" ${
        prevSort === "name" ? 'selected="selected"' : ""
      }>Name A-Z</option>
    </select>
    
    <p>Results per page:</p>
    <select name="limit" title="Limit">
      <option value="5">5 results</option>
      <option value="10">10 results</option>
      <option value="20">20 results</option>
    </select>
    
    <p>
      <anchor title="Search">Search
        <go href="/wml/chats.results.wml" method="get">
          <postfield name="q" value="$(q)"/>
          <postfield name="type" value="$(type)"/>
          <postfield name="sort" value="$(sort)"/>
          <postfield name="limit" value="$(limit)"/>
        </go>
      </anchor>
    </p>
    <do type="accept" label="${t('common.search')}">
      <go href="/wml/chats.results.wml" method="get">
        <postfield name="q" value="$(q)"/>
        <postfield name="type" value="$(type)"/>
        <postfield name="sort" value="$(sort)"/>
        <postfield name="limit" value="$(limit)"/>
      </go>
    </do>

    <p><b>Quick Searches:</b></p>
    <p>
      <a href="/wml/chats.wml?q=unread" accesskey="1">[1] Recent Activity</a><br/>
      <a href="/wml/chats.wml?groups=1&amp;direct=0" accesskey="2">[2] Groups Only</a><br/>
      <a href="/wml/chats.wml?groups=0&amp;direct=1" accesskey="3">[3] Direct Only</a><br/>
    </p>
    
    ${navigationBar()}
  `;

  sendWml(res, card("chats-search", "Chat Search", body));
});

// Chat search results
app.get("/wml/chats.results.wml", async (req, res) => {
  const q = String(req.query.q || "").trim();
  const chatType = req.query.type || "all";
  const sortBy = req.query.sort || "recent";
  const limit = 3; // Fisso a 3 elementi per pagina

  if (!q || q.length < 1) {
    sendWml(
      res,
      resultCard("Search Error", ["Query is required"], "/wml/chats.search.wml")
    );
    return;
  }

  // Build chat list synchronously (no async network calls) then filter+paginate first
  const searchLower = q.toLowerCase();
  let chats = [];
  for (const chatId of chatStore.keys()) {
    const isGroup = chatId.endsWith("@g.us");

    // Filter by type FIRST — skip early
    if (chatType === "direct" && isGroup) continue;
    if (chatType === "groups" && !isGroup) continue;

    const messages = chatStore.get(chatId) || [];
    const lastMessage = messages.length > 0 ? messages[messages.length - 1] : null;
    const phoneNumber = chatId.replace("@s.whatsapp.net", "").replace("@g.us", "");

    // Synchronous cached name (no network calls)
    const contact = contactStore.get(chatId) || {};
    const chatName = contact.subject || contact.name || contact.notify || contact.verifiedName || jidFriendly(chatId);
    const lastMessageText = lastMessage ? messageText(lastMessage) : "No messages";

    // Apply search filter inline — skip non-matching early
    const nameMatch = chatName.toLowerCase().includes(searchLower);
    const numberMatch = phoneNumber && phoneNumber.includes(searchLower);
    const messageMatch = lastMessageText.toLowerCase().includes(searchLower);
    if (!nameMatch && !numberMatch && !messageMatch) continue;

    chats.push({
      id: chatId,
      name: chatName,
      isGroup,
      phoneNumber: isGroup ? null : phoneNumber,
      messageCount: messages.length,
      lastMessage: {
        text: lastMessageText,
        timestamp: lastMessage ? Number(lastMessage.messageTimestamp) : 0,
      },
    });
  }

  // Sort results
  if (sortBy === "recent") {
    chats.sort((a, b) => b.lastMessage.timestamp - a.lastMessage.timestamp);
  } else if (sortBy === "messages") {
    chats.sort((a, b) => b.messageCount - a.messageCount);
  } else if (sortBy === "name") {
    chats.sort((a, b) => { const na = a.name.toLowerCase(), nb = b.name.toLowerCase(); return na < nb ? -1 : na > nb ? 1 : 0; });
  }

  const results = chats.slice(0, limit);

  // Resolve accurate names only for the visible results (max 3 async calls instead of ALL)
  await Promise.all(
    results.map(async (item) => {
      item.name = await getContactName(item.id, sock);
    })
  );

  const resultList =
    results
      .map((c, idx) => {
        const typeIcon = c.isGroup ? "[GROUP]" : "[CHAT]";
        const messagePreview = truncate(c.lastMessage.text, 50);
        const lastActivity =
          c.lastMessage.timestamp > 0
            ? new Date(c.lastMessage.timestamp * 1000).toLocaleString("en-GB", {
                day: "2-digit",
                month: "short",
                year: "numeric",
                hour: "2-digit",
                minute: "2-digit",
                second: "2-digit",
              })
            : "No activity";

        // Show both name and number/JID
        const displayNumber = c.phoneNumber || c.id.replace("@s.whatsapp.net", "").replace("@g.us", "");

        return `<p><b>${idx + 1}.</b> ${typeIcon} ${esc(c.name)}<br/>
      <small>${esc(displayNumber)}</small><br/>
      <small>${esc(messagePreview)}</small><br/>
      <small>${lastActivity} | ${c.messageCount} msgs</small><br/>
      <a href="/wml/chat.wml?jid=${encodeURIComponent(
        c.id
      )}&amp;limit=3">[Open]</a> |
      <a href="/wml/send.text.wml?to=${encodeURIComponent(c.id)}">[Send]</a>
    </p>`;
      })
      .join("") || "<p>No matching chats found.</p>";

  const body = `
    <p><b>Chat Search Results</b></p>
    <p>Query: <b>${esc(q)}</b></p>
    <p>Type: ${esc(chatType)} | Sort: ${esc(sortBy)}</p>
    <p>Found: ${results.length} of ${chats.length}</p>
    
    ${resultList}
    
    <p><b>Search Again:</b></p>
    <p>
      <a href="/wml/chats.search.wml?q=${encodeURIComponent(
        q
      )}" accesskey="1">[1] Modify Search</a> |
      <a href="/wml/chats.wml" accesskey="0">[0] All Chats</a>
    </p>
    
    <do type="accept" label="${t('common.back')}">
      <go href="/wml/chats.wml"/>
    </do>
  `;

  sendWml(res, card("chat-results", "Search Results", body));
});
app.get("/wml/sync.chats.wml", async (req, res) => {
  try {
    if (!sock) {
      sendWml(
        res,
        resultCard("Error", ["Not connected to WhatsApp"], "/wml/status.wml")
      );
      return;
    }

    const initialCount = chatStore.size;

    // Fetch groups (the main chat sync method available)
    const groups = await sock.groupFetchAllParticipating();
    Object.keys(groups).forEach((chatId) => {
      if (!chatStore.has(chatId)) {
        chatStore.set(chatId, []);
      }
    });

    await delay(2000); // Wait for additional chat events

    const finalCount = chatStore.size;
    const newChats = finalCount - initialCount;

    sendWml(
      res,
      resultCard(
        "Chat Sync Complete",
        [
          `Groups fetched: ${Object.keys(groups).length}`,
          `Initial chats: ${initialCount}`,
          `Final chats: ${finalCount}`,
          `New chats: ${newChats}`,
        ],
        "/wml/status.wml",
        true
      )
    );
  } catch (e) {
    sendWml(
      res,
      resultCard(
        "Chat Sync Failed",
        [e.message || "Failed to sync chats"],
        "/wml/status.wml"
      )
    );
  }
});

// =================== ERROR HANDLING & SERVER SETUP ===================

// Error handling
// Opera/WML error handler — returns HTML instead of JSON for browser-based routes
app.use((err, req, res, next) => {
  if (req.path.startsWith('/opera/') || req.path.startsWith('/wml/')) {
    console.error("Opera/WML Error:", err);
    const message = err.code === 'LIMIT_FILE_SIZE'
      ? t('opera.file_too_large_retry')
      : `${t('common.error')}: ${err.message}`;
    const jid = req.body?.to || req.body?.jid || null;
    res.status(err.code === 'LIMIT_FILE_SIZE' ? 413 : 500);
    res.setHeader("Content-Type", "text/html; charset=utf-8");
    res.setHeader("Cache-Control", "no-cache, no-store, must-revalidate");
    return res.send(operaResultPage(t('common.error'), message, jid));
  }
  next(err);
});

app.use((err, req, res, next) => {
  console.error("Server Error:", err);
  res.status(500).json({
    error: "Internal server error",
    details: NODE_ENV === "development" ? err.message : undefined,
  });
});

// 404 handler
app.use((req, res) => {
  res.status(404).json({
    error: "Endpoint not found",
    path: req.path,
    method: req.method,
    suggestion: "Check the API documentation for available endpoints",
  });
});

export { app, sock, contactStore, chatStore, messageStore };
