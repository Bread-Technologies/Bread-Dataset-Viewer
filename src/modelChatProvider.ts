import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { ensureBackendReady } from './backends';

interface ModelInfo {
    fileName: string;
    filePath: string;
    fileType: 'gguf' | 'safetensors';
    modelType?: string;
    architecture?: string;
    contextLength?: number;
}

export class ModelChatProvider implements vscode.CustomReadonlyEditorProvider {
    private activeModels = new Map<string, string>(); // webview id -> temp model name

    constructor(private readonly context: vscode.ExtensionContext) {}

    async openCustomDocument(
        uri: vscode.Uri,
        openContext: vscode.CustomDocumentOpenContext,
        token: vscode.CancellationToken
    ): Promise<vscode.CustomDocument> {
        return { uri, dispose: () => {} };
    }

    async resolveCustomEditor(
        document: vscode.CustomDocument,
        webviewPanel: vscode.WebviewPanel,
        token: vscode.CancellationToken
    ): Promise<void> {
        webviewPanel.webview.options = {
            enableScripts: true,
        };

        const modelInfo = await this.detectModelInfo(document.uri.fsPath);
        webviewPanel.webview.html = this.getHtmlForWebview(webviewPanel.webview, modelInfo);

        // Ensure backend is ready
        const backend = await ensureBackendReady();
        if (!backend) {
            webviewPanel.webview.postMessage({
                type: 'error',
                message: 'Backend not available. Please install Ollama.',
            });
            return;
        }

        // Load model if it's a GGUF file
        let modelName: string | null = null;
        if (modelInfo.fileType === 'gguf') {
            modelName = await this.loadModel(document.uri.fsPath, backend, webviewPanel.webview);
            if (modelName) {
                this.activeModels.set(webviewPanel.viewColumn?.toString() || 'default', modelName);
            }
        } else {
            // Safetensors - show message
            webviewPanel.webview.postMessage({
                type: 'info',
                message: 'Safetensors support requires conversion. Use GGUF for direct chat, or use a model from the Ollama library.',
            });
        }

        // Handle messages from webview
        webviewPanel.webview.onDidReceiveMessage(async (message) => {
            switch (message.type) {
                case 'sendMessage':
                    if (modelName) {
                        await this.handleChat(modelName, message.messages, webviewPanel.webview, backend);
                    }
                    break;
                case 'clearChat':
                    // Just acknowledge - webview handles clearing its own state
                    break;
            }
        });

        // Cleanup on close
        webviewPanel.onDidDispose(() => {
            const tempModelName = this.activeModels.get(webviewPanel.viewColumn?.toString() || 'default');
            if (tempModelName && backend) {
                backend.deleteModel(tempModelName).catch(err => {
                    console.error('Failed to cleanup model:', err);
                });
                this.activeModels.delete(webviewPanel.viewColumn?.toString() || 'default');
            }
        });
    }

    private async detectModelInfo(filePath: string): Promise<ModelInfo> {
        const fileName = path.basename(filePath);
        const ext = path.extname(filePath).toLowerCase();
        
        const info: ModelInfo = {
            fileName,
            filePath,
            fileType: ext === '.gguf' ? 'gguf' : 'safetensors',
        };

        if (ext === '.safetensors') {
            // Look for config.json
            const configPath = path.join(path.dirname(filePath), 'config.json');
            if (fs.existsSync(configPath)) {
                try {
                    const configContent = await fs.promises.readFile(configPath, 'utf8');
                    const config = JSON.parse(configContent);
                    
                    info.modelType = config.model_type;
                    info.architecture = config.architectures?.[0];
                    info.contextLength = config.max_position_embeddings;
                } catch (error) {
                    console.error('Failed to parse config.json:', error);
                }
            }
        }

        return info;
    }

    private async loadModel(
        filePath: string,
        backend: any,
        webview: vscode.Webview
    ): Promise<string | null> {
        const timestamp = Date.now();
        const modelName = `temp-model-${timestamp}`;

        return await vscode.window.withProgress(
            {
                location: vscode.ProgressLocation.Notification,
                title: 'Loading model...',
                cancellable: false,
            },
            async (progress) => {
                try {
                    progress.report({ message: 'Creating model in Ollama...' });
                    const success = await backend.createModel(filePath, modelName);
                    
                    if (success) {
                        webview.postMessage({
                            type: 'modelReady',
                            modelName,
                        });
                        vscode.window.showInformationMessage(`Model loaded: ${modelName}`);
                        return modelName;
                    } else {
                        webview.postMessage({
                            type: 'error',
                            message: 'Failed to load model',
                        });
                        return null;
                    }
                } catch (error) {
                    webview.postMessage({
                        type: 'error',
                        message: `Error loading model: ${error}`,
                    });
                    return null;
                }
            }
        );
    }

    private async handleChat(
        modelName: string,
        messages: any[],
        webview: vscode.Webview,
        backend: any
    ): Promise<void> {
        try {
            const stream = await backend.chat(modelName, messages);
            const reader = stream.getReader();
            const decoder = new TextDecoder();

            while (true) {
                const { done, value } = await reader.read();
                if (done) break;

                const chunk = decoder.decode(value);
                const lines = chunk.split('\n').filter(line => line.trim());

                for (const line of lines) {
                    try {
                        const json = JSON.parse(line);
                        if (json.message?.content) {
                            webview.postMessage({
                                type: 'token',
                                content: json.message.content,
                            });
                        }
                        if (json.done) {
                            webview.postMessage({
                                type: 'done',
                            });
                        }
                    } catch (e) {
                        // Skip malformed JSON
                    }
                }
            }
        } catch (error) {
            webview.postMessage({
                type: 'error',
                message: `Chat error: ${error}`,
            });
        }
    }

    private getHtmlForWebview(webview: vscode.Webview, modelInfo: ModelInfo): string {
        return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Model Chat</title>
    <style>
        * {
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }

        body {
            font-family: var(--vscode-font-family);
            font-size: var(--vscode-font-size);
            color: var(--vscode-foreground);
            background-color: var(--vscode-editor-background);
            display: flex;
            flex-direction: column;
            height: 100vh;
            overflow: hidden;
        }

        #header {
            background-color: var(--vscode-editorGroupHeader-tabsBackground);
            border-bottom: 1px solid var(--vscode-panel-border);
            padding: 12px 16px;
            flex-shrink: 0;
        }

        #model-info {
            display: flex;
            justify-content: space-between;
            align-items: center;
        }

        .model-name {
            font-weight: 600;
            font-size: 14px;
        }

        .model-details {
            font-size: 12px;
            color: var(--vscode-descriptionForeground);
        }

        .header-actions {
            display: flex;
            gap: 8px;
        }

        button {
            background-color: var(--vscode-button-background);
            color: var(--vscode-button-foreground);
            border: none;
            padding: 6px 12px;
            cursor: pointer;
            border-radius: 2px;
            font-size: 12px;
            transition: background-color 0.2s;
        }

        button:hover {
            background-color: var(--vscode-button-hoverBackground);
        }

        button:disabled {
            opacity: 0.5;
            cursor: not-allowed;
        }

        button.secondary {
            background-color: var(--vscode-button-secondaryBackground);
            color: var(--vscode-button-secondaryForeground);
        }

        button.secondary:hover {
            background-color: var(--vscode-button-secondaryHoverBackground);
        }

        #chat-container {
            flex: 1;
            overflow-y: auto;
            padding: 16px;
            display: flex;
            flex-direction: column;
            gap: 12px;
        }

        .message {
            display: flex;
            gap: 12px;
            max-width: 80%;
            animation: fadeIn 0.3s ease-in;
        }

        @keyframes fadeIn {
            from { opacity: 0; transform: translateY(10px); }
            to { opacity: 1; transform: translateY(0); }
        }

        .message.user {
            align-self: flex-end;
            flex-direction: row-reverse;
        }

        .message.assistant {
            align-self: flex-start;
        }

        .message-avatar {
            width: 32px;
            height: 32px;
            border-radius: 50%;
            display: flex;
            align-items: center;
            justify-content: center;
            flex-shrink: 0;
            font-size: 18px;
        }

        .message.user .message-avatar {
            background-color: var(--vscode-inputOption-activeBackground);
        }

        .message.assistant .message-avatar {
            background-color: var(--vscode-charts-blue);
        }

        .message-content {
            background-color: var(--vscode-editor-inactiveSelectionBackground);
            padding: 12px;
            border-radius: 8px;
            line-height: 1.5;
            word-wrap: break-word;
        }

        .message.user .message-content {
            background-color: var(--vscode-inputOption-activeBackground);
        }

        .typing-indicator {
            display: none;
            align-items: center;
            gap: 4px;
            padding: 12px;
            color: var(--vscode-descriptionForeground);
        }

        .typing-indicator.active {
            display: flex;
        }

        .typing-dot {
            width: 8px;
            height: 8px;
            border-radius: 50%;
            background-color: var(--vscode-descriptionForeground);
            animation: typing 1.4s infinite;
        }

        .typing-dot:nth-child(2) {
            animation-delay: 0.2s;
        }

        .typing-dot:nth-child(3) {
            animation-delay: 0.4s;
        }

        @keyframes typing {
            0%, 60%, 100% { transform: translateY(0); }
            30% { transform: translateY(-10px); }
        }

        #input-container {
            border-top: 1px solid var(--vscode-panel-border);
            padding: 16px;
            background-color: var(--vscode-editorGroupHeader-tabsBackground);
            flex-shrink: 0;
        }

        #input-form {
            display: flex;
            gap: 8px;
        }

        #message-input {
            flex: 1;
            background-color: var(--vscode-input-background);
            color: var(--vscode-input-foreground);
            border: 1px solid var(--vscode-input-border);
            padding: 10px 12px;
            border-radius: 4px;
            font-family: var(--vscode-font-family);
            font-size: 13px;
            resize: none;
            min-height: 40px;
            max-height: 200px;
        }

        #message-input:focus {
            outline: 1px solid var(--vscode-focusBorder);
        }

        #send-btn {
            padding: 10px 20px;
            align-self: flex-end;
        }

        .info-message, .error-message {
            text-align: center;
            padding: 16px;
            margin: 16px;
            border-radius: 4px;
        }

        .info-message {
            background-color: var(--vscode-inputValidation-infoBackground);
            border: 1px solid var(--vscode-inputValidation-infoBorder);
            color: var(--vscode-inputValidation-infoForeground);
        }

        .error-message {
            background-color: var(--vscode-inputValidation-errorBackground);
            border: 1px solid var(--vscode-inputValidation-errorBorder);
            color: var(--vscode-errorForeground);
        }

        .empty-state {
            flex: 1;
            display: flex;
            flex-direction: column;
            align-items: center;
            justify-content: center;
            color: var(--vscode-descriptionForeground);
            text-align: center;
            padding: 32px;
        }

        .empty-state-icon {
            font-size: 48px;
            margin-bottom: 16px;
        }

        .empty-state-title {
            font-size: 18px;
            font-weight: 600;
            margin-bottom: 8px;
        }

        .empty-state-description {
            font-size: 13px;
            max-width: 400px;
        }
    </style>
</head>
<body>
    <div id="header">
        <div id="model-info">
            <div>
                <div class="model-name">${modelInfo.fileName}</div>
                <div class="model-details">
                    ${modelInfo.fileType.toUpperCase()}
                    ${modelInfo.contextLength ? ` • Context: ${modelInfo.contextLength} tokens` : ''}
                    ${modelInfo.architecture ? ` • ${modelInfo.architecture}` : ''}
                </div>
            </div>
            <div class="header-actions">
                <button id="clear-btn" class="secondary">Clear Chat</button>
            </div>
        </div>
    </div>

    <div id="chat-container">
        <div class="empty-state" id="empty-state">
            <div class="empty-state-icon">💬</div>
            <div class="empty-state-title">Start a conversation</div>
            <div class="empty-state-description">
                Type a message below to start chatting with this model.
            </div>
        </div>
    </div>

    <div id="input-container">
        <form id="input-form">
            <textarea 
                id="message-input" 
                placeholder="Type a message..." 
                rows="1"
            ></textarea>
            <button type="submit" id="send-btn">Send</button>
        </form>
    </div>

    <script>
        const vscode = acquireVsCodeApi();
        
        let messages = [];
        let isWaitingForResponse = false;
        let currentAssistantMessage = null;
        let modelReady = false;

        const chatContainer = document.getElementById('chat-container');
        const messageInput = document.getElementById('message-input');
        const sendBtn = document.getElementById('send-btn');
        const clearBtn = document.getElementById('clear-btn');
        const inputForm = document.getElementById('input-form');
        const emptyState = document.getElementById('empty-state');

        // Auto-resize textarea
        messageInput.addEventListener('input', () => {
            messageInput.style.height = 'auto';
            messageInput.style.height = messageInput.scrollHeight + 'px';
        });

        // Handle form submission
        inputForm.addEventListener('submit', (e) => {
            e.preventDefault();
            sendMessage();
        });

        // Handle Enter key (Shift+Enter for newline)
        messageInput.addEventListener('keydown', (e) => {
            if (e.key === 'Enter' && !e.shiftKey) {
                e.preventDefault();
                sendMessage();
            }
        });

        clearBtn.addEventListener('click', () => {
            messages = [];
            chatContainer.innerHTML = '';
            chatContainer.appendChild(emptyState);
            emptyState.style.display = 'flex';
            vscode.postMessage({ type: 'clearChat' });
        });

        function sendMessage() {
            const content = messageInput.value.trim();
            if (!content || isWaitingForResponse || !modelReady) return;

            // Hide empty state
            emptyState.style.display = 'none';

            // Add user message
            messages.push({ role: 'user', content });
            addMessageToUI('user', content);

            // Clear input
            messageInput.value = '';
            messageInput.style.height = 'auto';

            // Show typing indicator
            isWaitingForResponse = true;
            sendBtn.disabled = true;
            messageInput.disabled = true;

            // Create placeholder for assistant response
            currentAssistantMessage = addMessageToUI('assistant', '');
            showTypingIndicator();

            // Send to backend
            vscode.postMessage({
                type: 'sendMessage',
                messages: messages,
            });
        }

        function addMessageToUI(role, content) {
            const messageDiv = document.createElement('div');
            messageDiv.className = \`message \${role}\`;

            const avatar = document.createElement('div');
            avatar.className = 'message-avatar';
            avatar.textContent = role === 'user' ? '👤' : '🤖';

            const contentDiv = document.createElement('div');
            contentDiv.className = 'message-content';
            contentDiv.textContent = content;

            messageDiv.appendChild(avatar);
            messageDiv.appendChild(contentDiv);

            chatContainer.appendChild(messageDiv);
            chatContainer.scrollTop = chatContainer.scrollHeight;

            return contentDiv;
        }

        function showTypingIndicator() {
            // For simplicity, we'll just show "..." in the message
            if (currentAssistantMessage) {
                currentAssistantMessage.textContent = '...';
            }
        }

        // Handle messages from extension
        window.addEventListener('message', event => {
            const message = event.data;

            switch (message.type) {
                case 'modelReady':
                    modelReady = true;
                    messageInput.disabled = false;
                    sendBtn.disabled = false;
                    break;

                case 'token':
                    if (currentAssistantMessage) {
                        if (currentAssistantMessage.textContent === '...') {
                            currentAssistantMessage.textContent = '';
                        }
                        currentAssistantMessage.textContent += message.content;
                        chatContainer.scrollTop = chatContainer.scrollHeight;
                    }
                    break;

                case 'done':
                    if (currentAssistantMessage) {
                        messages.push({
                            role: 'assistant',
                            content: currentAssistantMessage.textContent,
                        });
                    }
                    isWaitingForResponse = false;
                    currentAssistantMessage = null;
                    sendBtn.disabled = false;
                    messageInput.disabled = false;
                    messageInput.focus();
                    break;

                case 'error':
                    const errorDiv = document.createElement('div');
                    errorDiv.className = 'error-message';
                    errorDiv.textContent = '❌ ' + message.message;
                    chatContainer.appendChild(errorDiv);
                    
                    isWaitingForResponse = false;
                    currentAssistantMessage = null;
                    sendBtn.disabled = false;
                    messageInput.disabled = false;
                    break;

                case 'info':
                    const infoDiv = document.createElement('div');
                    infoDiv.className = 'info-message';
                    infoDiv.textContent = 'ℹ️ ' + message.message;
                    chatContainer.appendChild(infoDiv);
                    break;
            }
        });

        // Focus input on load
        messageInput.focus();
    </script>
</body>
</html>`;
    }
}
