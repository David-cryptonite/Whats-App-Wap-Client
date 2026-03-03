// persistentStorage.js - ESM version for Baileys 7.x
import fs from 'fs';
import path from 'path';

class PersistentStorage {
  constructor(dataDir = './data') {
    this.dataDir = dataDir
    this.contactsFile = path.join(dataDir, 'contacts.json')
    this.chatsFile = path.join(dataDir, 'chats.json')
    this.messagesFile = path.join(dataDir, 'messages.json')
    this.metaFile = path.join(dataDir, 'meta.json')
    this.settingsFile = path.join(dataDir, 'settings.json')
    
    // Ensure data directory exists
    if (!fs.existsSync(dataDir)) {
      fs.mkdirSync(dataDir, { recursive: true })
    }
    
    this.saveQueue = new Map()
    this.isProcessing = false
  }

  // Load data from files on startup
  loadAllData() {
    const result = {
      contacts: new Map(),
      chats: new Map(),
      messages: new Map(),
      meta: {
        lastSync: null,
        isFullySynced: false,
        syncAttempts: 0
      }
    }

    try {
      // Load contacts
      if (fs.existsSync(this.contactsFile)) {
        const contactsData = JSON.parse(fs.readFileSync(this.contactsFile, 'utf8'))

        // Separate JID and LID contacts
        const jidContacts = contactsData.filter(([key]) => !key.startsWith('lid:'))
        const lidContacts = contactsData.filter(([key]) => key.startsWith('lid:'))

        // Load JID contacts first, then LID contacts
        result.contacts = new Map([...jidContacts, ...lidContacts])

        console.log(`📱 Loaded ${result.contacts.size} contacts from disk (${jidContacts.length} JID, ${lidContacts.length} LID)`)
      }

      // Load chats
      if (fs.existsSync(this.chatsFile)) {
        const chatsData = JSON.parse(fs.readFileSync(this.chatsFile, 'utf8'))

        // Separate JID and LID chats
        const jidChats = chatsData.filter(([key]) => !key.startsWith('lid:'))
        const lidChats = chatsData.filter(([key]) => key.startsWith('lid:'))

        // Load JID chats first, then LID chats
        result.chats = new Map([...jidChats, ...lidChats].map(([key, messages]) => [key, messages]))

        console.log(`💬 Loaded ${result.chats.size} chats from disk (${jidChats.length} JID, ${lidChats.length} LID)`)
      }

      // Load messages
      if (fs.existsSync(this.messagesFile)) {
        const messagesData = JSON.parse(fs.readFileSync(this.messagesFile, 'utf8'))
        result.messages = new Map(messagesData)
        console.log(`📨 Loaded ${result.messages.size} messages from disk`)
      }

      // Load metadata
      if (fs.existsSync(this.metaFile)) {
        const metaData = JSON.parse(fs.readFileSync(this.metaFile, 'utf8'))
        result.meta = { ...result.meta, ...metaData }
        console.log(`⚙️ Loaded metadata from disk`)
      }

      // Load settings
      if (fs.existsSync(this.settingsFile)) {
        result.settings = JSON.parse(fs.readFileSync(this.settingsFile, 'utf8'))
        console.log(`⚙️ Loaded settings from disk`)
      }

      console.log(`✅ Successfully loaded all data from persistent storage`)
      return result
    } catch (error) {
      console.error(`❌ Error loading data from disk:`, error.message)
      return result // Return empty maps if loading fails
    }
  }

  // Queue a save operation (debounced to avoid excessive writes)
  queueSave(type, data) {
    this.saveQueue.set(type, data)

    // Process queue after a short delay (debounce multiple rapid saves)
    if (!this.isProcessing) {
      this.isProcessing = true
      setTimeout(() => this.processSaveQueue(), 100) // 100ms debounce (ridotto da 2000ms per evitare perdita dati)
    }
  }

  // Process all queued save operations
  async processSaveQueue() {
    const operations = Array.from(this.saveQueue.entries())
    this.saveQueue.clear()
    this.isProcessing = false

    for (const [type, data] of operations) {
      try {
        await this.saveToFile(type, data)
      } catch (error) {
        console.error(`❌ Failed to save ${type}:`, error.message)
      }
    }
  }

  // Save data to appropriate file
  async saveToFile(type, data) {
    let filePath, serializedData

    switch (type) {
      case 'contacts':
        filePath = this.contactsFile
        serializedData = JSON.stringify(Array.from(data.entries()), null, 2)
        break
      
      case 'chats':
        filePath = this.chatsFile
        // Convert Map to array format for JSON serialization
        serializedData = JSON.stringify(Array.from(data.entries()), null, 2)
        break
      
      case 'messages':
        filePath = this.messagesFile
        serializedData = JSON.stringify(Array.from(data.entries()), null, 2)
        break
      
      case 'meta':
        filePath = this.metaFile
        serializedData = JSON.stringify(data, null, 2)
        break

      case 'settings':
        filePath = this.settingsFile
        serializedData = JSON.stringify(data, null, 2)
        break

      default:
        console.warn(`⚠️ Unknown save type: ${type}`)
        return
    }

    // Ensure data directory exists before saving
    if (!fs.existsSync(this.dataDir)) {
      fs.mkdirSync(this.dataDir, { recursive: true })
      console.log(`📁 Created data directory: ${this.dataDir}`)
    }

    // Write to temporary file first, then rename (atomic operation)
    const tempFile = `${filePath}.tmp`
    try {
      fs.writeFileSync(tempFile, serializedData, 'utf8')
      fs.renameSync(tempFile, filePath)
      console.log(`💾 Saved ${type} to disk`)
    } catch (error) {
      // If atomic operation fails, try direct write as fallback
      console.warn(`⚠️ Atomic save failed for ${type}, trying direct write:`, error.message)
      fs.writeFileSync(filePath, serializedData, 'utf8')
      console.log(`💾 Saved ${type} to disk (direct write)`)

      // Clean up temp file if it exists
      try {
        if (fs.existsSync(tempFile)) {
          fs.unlinkSync(tempFile)
        }
      } catch (cleanupError) {
        // Ignore cleanup errors
      }
    }
  }

  // Immediate save (for critical data)
  saveImmediately(type, data) {
    return this.saveToFile(type, data)
  }

  // Force immediate save of all queued operations (for shutdown)
  async flushQueue() {
    if (this.saveQueue.size > 0) {
      console.log(`🔄 Flushing ${this.saveQueue.size} queued save operations...`)
      await this.processSaveQueue()
    }
  }

  // Clean up old message data to prevent files from growing too large
  cleanupOldMessages(messageStore, chatStore, maxMessagesPerChat = 100) {
    let cleaned = 0
    
    for (const [chatId, messages] of chatStore.entries()) {
      if (messages.length > maxMessagesPerChat) {
        // Keep only the most recent messages
        const oldMessages = messages.splice(0, messages.length - maxMessagesPerChat)
        
        // Remove old message references from messageStore
        for (const msg of oldMessages) {
          if (msg.key?.id && messageStore.has(msg.key.id)) {
            messageStore.delete(msg.key.id)
            cleaned++
          }
        }
      }
    }
    
    if (cleaned > 0) {
      console.log(`🧹 Cleaned up ${cleaned} old messages`)
      this.queueSave('messages', messageStore)
      this.queueSave('chats', chatStore)
    }
  }

  // Export data for backup
  exportData() {
    const timestamp = new Date().toISOString().replace(/[:.]/g, '-')
    const backupDir = path.join(this.dataDir, 'backups')
    
    if (!fs.existsSync(backupDir)) {
      fs.mkdirSync(backupDir, { recursive: true })
    }
    
    const backupFile = path.join(backupDir, `backup-${timestamp}.json`)
    const data = this.loadAllData()
    
    const exportData = {
      timestamp: new Date().toISOString(),
      contacts: Array.from(data.contacts.entries()),
      chats: Array.from(data.chats.entries()),
      messages: Array.from(data.messages.entries()),
      meta: data.meta
    }
    
    fs.writeFileSync(backupFile, JSON.stringify(exportData, null, 2))
    console.log(`📦 Data exported to ${backupFile}`)
    
    return backupFile
  }
}

// ESM export - use both named and default for compatibility
export { PersistentStorage };
export default PersistentStorage;