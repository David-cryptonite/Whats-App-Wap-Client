// =================== CHAT HISTORY UTILITIES (ESM) ===================
// Module-level dependencies - will be set by serverWml.js
let logger = console; // Default to console
let sock = null;
let chatStore = null;
let messageStore = null;
let connectionState = 'disconnected';
let formatJid = (jid) => jid;
let delay = (ms) => new Promise(resolve => setTimeout(resolve, ms));
let saveMessageToDB = () => {};
let performInitialSync = async () => {};

// Initialize dependencies from main server
function initializeDependencies(deps) {
  logger = deps.logger || console;
  sock = deps.sock;
  chatStore = deps.chatStore;
  messageStore = deps.messageStore;
  connectionState = deps.connectionState;
  formatJid = deps.formatJid;
  delay = deps.delay;
  saveMessageToDB = deps.saveMessageToDB;
  performInitialSync = deps.performInitialSync;
}

// Getter for dynamic sock access
function getSock() {
  return sock;
}

function getConnectionState() {
  return connectionState;
}

async function loadChatHistory(jid, batchSize = 99999999999999) {
  // DISABLED: Chat history is loaded from persistent storage
  // No need to fetch from WhatsApp servers - causes spam and slowdown
  return [];
}




// =================== FUNZIONI DI SUPPORTO ===================

async function loadAllChatsHistory(maxChatsToLoad = 50, messagesPerChat = 100) {
  // DISABLED: Chat history is loaded from persistent storage at startup
  logger.info('loadAllChatsHistory disabled - using persistent storage instead');
  return false;
}

async function loadRecentMessages(jid, hours = 24) {
  // DISABLED: Messages are loaded from persistent storage at startup
  logger.info('loadRecentMessages disabled - using persistent storage instead');
  return [];
}

async function preloadImportantChats() {
  // DISABLED: All chats are already loaded from persistent storage at startup
  logger.info('preloadImportantChats disabled - using persistent storage instead');
  return;
}

// Integrazione nel sistema esistente
async function enhancedInitialSync() {
  try {
    logger.info('Starting enhanced sync with message history loading (4GB RAM optimized)...');

    // Prima esegui la sync base
    if (performInitialSync) {
      await performInitialSync();
    }

    // Poi carica la cronologia dei messaggi - ottimizzato per 4GB RAM
    if (chatStore && chatStore.size > 0) {
      logger.info('Loading chat histories (4GB RAM mode)...');

      // Carica cronologia per 30 chat con 100 messaggi ciascuna
      // 4GB RAM può gestire molto più dati
      await loadAllChatsHistory(999999999999999999, 999999999999999999999);

      // Precarica le 10 chat più importanti
      await preloadImportantChats();

      logger.info('Enhanced sync completed successfully (4GB RAM mode)');
    }

  } catch (error) {
    logger.error('Enhanced sync failed:', error.message);
  }
}

// Export functions (ESM)
export {
  initializeDependencies,
  getSock,
  getConnectionState,
  loadChatHistory,
  loadAllChatsHistory,
  loadRecentMessages,
  preloadImportantChats,
  enhancedInitialSync
};
