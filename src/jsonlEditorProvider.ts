import * as vscode from 'vscode';
import * as fs from 'fs';
import * as readline from 'readline';
import * as path from 'path';
import { countTokens } from './utils/tokenizer';

export class JsonlEditorProvider implements vscode.CustomReadonlyEditorProvider {
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
        const startTime = Date.now();
        
        webviewPanel.webview.options = {
            enableScripts: true,
        };

        console.log(`[PERF] Options set: ${Date.now() - startTime}ms`);
        
        webviewPanel.webview.html = this.getHtmlForWebview(webviewPanel.webview);
        
        console.log(`[PERF] HTML set: ${Date.now() - startTime}ms`);

        // Get file stats
        const stats = await fs.promises.stat(document.uri.fsPath);
        const fileSizeBytes = stats.size;
        const fileSizeMB = (fileSizeBytes / 1024 / 1024).toFixed(2);

        console.log(`[PERF] Stats read: ${Date.now() - startTime}ms`);
        
        // Send initial file info with timestamp
        webviewPanel.webview.postMessage({
            type: 'fileInfo',
            filePath: document.uri.fsPath,
            fileName: path.basename(document.uri.fsPath),
            fileSize: fileSizeBytes,
            fileSizeMB: fileSizeMB,
            backendTimestamp: Date.now(), // When backend sent this
            backendTimeSinceStart: Date.now() - startTime, // Time from click
        });
        
        console.log(`[PERF] File info sent: ${Date.now() - startTime}ms`);

        // Handle messages from webview
        webviewPanel.webview.onDidReceiveMessage(async (message) => {
            switch (message.type) {
                case 'loadLines':
                    await this.loadLines(
                        document.uri.fsPath,
                        webviewPanel.webview,
                        message.offset,
                        message.limit,
                        message.searchTerm,
                        message.tokenizer
                    );
                    break;
                case 'jumpToLine':
                    await this.jumpToLine(
                        document.uri.fsPath,
                        webviewPanel.webview,
                        message.lineNumber,
                        message.tokenizer
                    );
                    break;
                case 'openInTextEditor':
                    // Open the file in the default text editor
                    const doc = await vscode.workspace.openTextDocument(document.uri);
                    await vscode.window.showTextDocument(doc, { preview: false });
                    break;
            }
        });

        // Load initial batch
        await this.loadLines(document.uri.fsPath, webviewPanel.webview, 0, 100);
        
        console.log(`[PERF] Initial lines loaded: ${Date.now() - startTime}ms`);
    }

    private async loadLines(
        filePath: string,
        webview: vscode.Webview,
        offset: number = 0,
        limit: number = 10,
        searchTerm?: string,
        tokenizer: string = 'gpt-4'
    ): Promise<void> {
        const loadStart = Date.now();
        try {
            const stream = fs.createReadStream(filePath, { encoding: 'utf8' });
            const rl = readline.createInterface({ input: stream });

            let lineNum = 0; // Start at 0 for zero-based indexing
            const lines: any[] = [];
            let skippedBySearch = 0;

            for await (const line of rl) {
                // Skip lines before offset
                if (lineNum < offset) {
                    lineNum++;
                    continue;
                }

                // Stop if we have enough lines
                if (lines.length >= limit) {
                    break;
                }

                // Apply search filter if present
                if (searchTerm && !line.toLowerCase().includes(searchTerm.toLowerCase())) {
                    skippedBySearch++;
                    lineNum++;
                    continue;
                }

                try {
                    const data = JSON.parse(line);
                    lines.push({ index: lineNum, data, raw: line });
                } catch {
                    // Handle malformed JSON
                    lines.push({ index: lineNum, data: null, raw: line, error: true });
                }

                lineNum++;
            }

            rl.close();
            stream.destroy();

            console.log(`[PERF] File read complete: ${Date.now() - loadStart}ms (${lines.length} lines)`);

            // Send lines immediately without tokens
            const linesSentTime = Date.now();
            webview.postMessage({
                type: 'lines',
                lines,
                hasMore: lines.length === limit,
                nextOffset: lineNum,
                searchTerm,
                skippedBySearch,
                backendTimestamp: linesSentTime, // When backend sent this
            });
            
            console.log(`[PERF] Lines message sent: ${Date.now() - loadStart}ms`);

            // Calculate tokens in background and send separately
            setImmediate(() => {
                const tokenStart = Date.now();
                const tokensMap: { [key: number]: number } = {};
                for (const line of lines) {
                    tokensMap[line.index] = countTokens(line.raw, tokenizer);
                }
                console.log(`[PERF] Token counting done: ${Date.now() - tokenStart}ms for ${lines.length} lines`);
                
                webview.postMessage({
                    type: 'tokens',
                    tokens: tokensMap,
                });
                
                console.log(`[PERF] Tokens message sent: ${Date.now() - tokenStart}ms`);
            });
        } catch (error) {
            webview.postMessage({
                type: 'error',
                message: `Failed to load file: ${error}`,
            });
        }
    }

    private async jumpToLine(
        filePath: string,
        webview: vscode.Webview,
        targetLine: number,
        tokenizer: string = 'gpt-4'
    ): Promise<void> {
        // For jump-to-line, we load from that line
        await this.loadLines(filePath, webview, targetLine, 100, undefined, tokenizer);
    }

    private getHtmlForWebview(webview: vscode.Webview): string {
        // Return full HTML - the async loading approach was causing issues
        // The webview initialization overhead is mostly VS Code's service worker,
        // which we can't optimize. The actual HTML parsing is fast.
        return this.getFullHtmlContent();
    }
    
    private getFullHtmlContent(): string {
        return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>JSONL Viewer</title>
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
            padding: 16px;
            overflow-x: hidden;
        }

        #toolbar {
            position: sticky;
            top: 0;
            background-color: var(--vscode-editor-background);
            border-bottom: 1px solid var(--vscode-panel-border);
            padding: 12px 0;
            margin-bottom: 16px;
            z-index: 100;
            display: flex;
            flex-wrap: wrap;
            gap: 12px;
            align-items: center;
        }

        .toolbar-section {
            display: flex;
            gap: 8px;
            align-items: center;
        }

        .toolbar-divider {
            width: 1px;
            height: 24px;
            background-color: var(--vscode-panel-border);
        }

        button {
            background-color: var(--vscode-button-background);
            color: var(--vscode-button-foreground);
            border: none;
            padding: 6px 12px;
            cursor: pointer;
            border-radius: 2px;
            font-size: 13px;
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

        button.active {
            background-color: var(--vscode-inputOption-activeBackground);
            border: 1px solid var(--vscode-inputOption-activeBorder);
        }

        input[type="text"], input[type="number"], select {
            background-color: var(--vscode-input-background);
            color: var(--vscode-input-foreground);
            border: 1px solid var(--vscode-input-border);
            padding: 6px 8px;
            border-radius: 2px;
            font-size: 13px;
            min-width: 200px;
        }

        select {
            min-width: auto;
            cursor: pointer;
        }

        input[type="text"]:focus, input[type="number"]:focus, select:focus {
            outline: 1px solid var(--vscode-focusBorder);
        }

        .stats {
            font-size: 12px;
            color: var(--vscode-descriptionForeground);
            display: flex;
            gap: 16px;
        }

        .stat-item {
            display: flex;
            gap: 4px;
        }

        .stat-label {
            font-weight: 600;
        }

        #container {
            max-width: 100%;
        }

        /* Card View Styles */
        .card {
            background-color: var(--vscode-editor-background);
            border: 1px solid var(--vscode-panel-border);
            border-radius: 4px;
            padding: 16px;
            margin-bottom: 12px;
        }

        .card-header {
            display: flex;
            justify-content: space-between;
            align-items: center;
            margin-bottom: 12px;
            padding-bottom: 8px;
            border-bottom: 1px solid var(--vscode-panel-border);
        }

        .card-title {
            font-size: 12px;
            color: var(--vscode-descriptionForeground);
            font-weight: 600;
        }

        .card-tokens {
            font-size: 11px;
            color: var(--vscode-badge-foreground);
            background-color: var(--vscode-badge-background);
            padding: 2px 8px;
            border-radius: 10px;
            font-weight: 500;
        }

        .card-content {
            font-family: var(--vscode-editor-font-family);
            font-size: 13px;
            line-height: 1.6;
            overflow-x: auto;
        }

        .card-error {
            border-left: 3px solid var(--vscode-errorForeground);
            background-color: var(--vscode-inputValidation-errorBackground);
        }

        .error-message {
            color: var(--vscode-errorForeground);
            font-size: 12px;
            margin-bottom: 8px;
        }

        /* JSON Syntax Highlighting */
        .json-key {
            color: #9cdcfe;
        }

        .json-string {
            color: #ce9178;
        }

        .json-number {
            color: #b5cea8;
        }

        .json-boolean {
            color: #569cd6;
        }

        .json-null {
            color: #569cd6;
        }

        /* Table View Styles */
        #table-container {
            display: none;
            overflow-x: auto;
        }

        /* Raw View Styles */
        #raw-container {
            display: none;
        }

        .raw-line {
            font-family: var(--vscode-editor-font-family);
            font-size: 13px;
            line-height: 1.8;
            padding: 2px 0;
            white-space: pre-wrap;
            word-wrap: break-word;
        }

        .raw-line-number {
            display: inline-block;
            min-width: 60px;
            color: var(--vscode-editorLineNumber-foreground);
            user-select: none;
            margin-right: 16px;
            text-align: right;
        }

        .raw-line-content {
            color: var(--vscode-editor-foreground);
        }

        table {
            width: 100%;
            border-collapse: collapse;
            font-size: 13px;
        }

        thead {
            position: sticky;
            top: 0;
            background-color: var(--vscode-editor-background);
            z-index: 10;
        }

        th {
            text-align: left;
            padding: 12px;
            border-bottom: 2px solid var(--vscode-panel-border);
            font-weight: 600;
            white-space: nowrap;
        }

        td {
            padding: 12px;
            border-bottom: 1px solid var(--vscode-panel-border);
            max-width: 300px;
            overflow: hidden;
            text-overflow: ellipsis;
            white-space: nowrap;
        }

        tr:hover {
            background-color: var(--vscode-list-hoverBackground);
        }

        .line-number-col {
            width: 80px;
            color: var(--vscode-descriptionForeground);
            font-family: var(--vscode-editor-font-family);
        }

        .tokens-col {
            width: 100px;
            text-align: right;
            color: var(--vscode-charts-blue);
        }

        /* Load More Button */
        .load-more-container {
            text-align: center;
            padding: 24px 0;
        }

        .load-more-container button {
            padding: 10px 24px;
            font-size: 14px;
        }

        .loading {
            text-align: center;
            padding: 24px 0;
            color: var(--vscode-descriptionForeground);
        }

        .jump-to-line {
            display: flex;
            gap: 4px;
            align-items: center;
        }

        .jump-to-line input {
            width: 100px;
            min-width: 100px;
        }
    </style>
</head>
<body>
    <div id="toolbar">
        <div class="toolbar-section">
            <strong id="file-name"></strong>
            <span style="font-size: 11px; color: var(--vscode-descriptionForeground);" id="file-size"></span>
        </div>
        
        <div class="toolbar-divider"></div>
        
        <div class="toolbar-section">
            <button id="card-view-btn" class="secondary active">📇 Cards</button>
            <button id="table-view-btn" class="secondary">📊 Table</button>
            <button id="raw-view-btn" class="secondary">📄 Raw</button>
        </div>
        
        <div class="toolbar-divider"></div>
        
        <div class="toolbar-section">
            <button id="edit-btn" class="secondary">✏️ Edit in Text Editor</button>
        </div>
        
        <div class="toolbar-divider"></div>
        
        <div class="toolbar-section">
            <label for="tokenizer-select" style="font-size: 12px; margin-right: 4px;" title="Select model tokenizer. For chat completions format, applies model-specific chat template before counting tokens.">Tokenizer:</label>
            <select id="tokenizer-select" title="OpenAI models use exact tokenizers. Other models use approximations with chat templates applied for chat completions format.">
                <option value="gpt-4">Loading...</option>
            </select>
        </div>
        
        <div class="toolbar-divider"></div>
        
        <div class="toolbar-section">
            <input type="text" id="search-input" placeholder="Search records...">
            <button id="search-btn" class="secondary">🔍 Search</button>
            <button id="clear-search-btn" class="secondary">✕ Clear</button>
        </div>
        
        <div class="toolbar-divider"></div>
        
        <div class="toolbar-section jump-to-line">
            <span style="font-size: 12px;">Jump to line:</span>
            <input type="number" id="jump-line-input" placeholder="Line #" min="0">
            <button id="jump-btn" class="secondary">Go</button>
        </div>
        
        <div class="toolbar-divider"></div>
        
        <div class="stats" id="stats">
            <div class="stat-item">
                <span class="stat-label">Loaded:</span>
                <span id="loaded-count">0</span>
            </div>
            <div class="stat-item">
                <span class="stat-label">Avg Tokens:</span>
                <span id="avg-tokens">-</span>
            </div>
            <div class="stat-item">
                <span class="stat-label">Max Tokens:</span>
                <span id="max-tokens">-</span>
            </div>
        </div>
    </div>

    <div id="container">
        <div id="cards-container"></div>
        <div id="table-container">
            <table id="data-table">
                <thead id="table-head"></thead>
                <tbody id="table-body"></tbody>
            </table>
        </div>
        <div id="raw-container"></div>
        <div class="load-more-container" id="load-more-container" style="display: none;">
            <button id="load-more-btn">Load More (100 lines)</button>
        </div>
        <div class="loading" id="loading" style="display: none;">Loading...</div>
    </div>

    <script>
        // CRITICAL: Set up message listener IMMEDIATELY (before anything else)
        // This ensures we can receive messages as soon as the webview is ready
        const vscode = acquireVsCodeApi();
        let messageQueue = [];
        let messageHandlerReady = false;
        
        // Set up message listener in the earliest possible moment (before DOM is ready)
        // This ensures we catch messages as soon as the webview can receive them
        const earlyMessageListener = (event) => {
            if (!messageHandlerReady || !window.handleMessage) {
                // Queue messages until handler is ready
                messageQueue.push(event.data);
            } else {
                // Handler is ready, process immediately
                window.handleMessage(event.data);
            }
        };
        window.addEventListener('message', earlyMessageListener, { capture: true, passive: true });
        
        let allLines = [];
        let nextOffset = 0;
        let hasMore = false;
        let currentView = 'cards';
        let currentSearchTerm = '';
        let fileInfo = null;
        let tokenCounts = new Map();
        let currentTokenizer = 'gpt-4';
        let listenersInitialized = false;
        
        // Defer non-critical event listeners until after first render
        function initializeEventListeners() {
            if (listenersInitialized) return;
            listenersInitialized = true;
            
            document.getElementById('card-view-btn').addEventListener('click', () => switchView('cards'));
            document.getElementById('table-view-btn').addEventListener('click', () => switchView('table'));
            document.getElementById('raw-view-btn').addEventListener('click', () => switchView('raw'));
            document.getElementById('search-btn').addEventListener('click', performSearch);
            document.getElementById('clear-search-btn').addEventListener('click', clearSearch);
            document.getElementById('load-more-btn').addEventListener('click', loadMore);
            document.getElementById('jump-btn').addEventListener('click', jumpToLine);
            document.getElementById('tokenizer-select').addEventListener('change', handleTokenizerChange);
            document.getElementById('edit-btn').addEventListener('click', openInTextEditor);
            
            document.getElementById('search-input').addEventListener('keypress', (e) => {
                if (e.key === 'Enter') performSearch();
            });
            
            document.getElementById('jump-line-input').addEventListener('keypress', (e) => {
                if (e.key === 'Enter') jumpToLine();
            });
            
            // Lazy load tokenizer options on first interaction
            const tokenizerSelect = document.getElementById('tokenizer-select');
            const loadOnInteraction = () => {
                if (tokenizerSelect.children.length <= 1) {
                    loadTokenizerOptions();
                }
                tokenizerSelect.removeEventListener('focus', loadOnInteraction);
                tokenizerSelect.removeEventListener('click', loadOnInteraction);
            };
            tokenizerSelect.addEventListener('focus', loadOnInteraction, { once: true });
            tokenizerSelect.addEventListener('click', loadOnInteraction, { once: true });
        }
        
        // Lazy load tokenizer dropdown options
        function loadTokenizerOptions() {
            const select = document.getElementById('tokenizer-select');
            select.innerHTML = \`
                <optgroup label="OpenAI Models (Exact)">
                    <option value="gpt-4">GPT-4 / GPT-3.5-Turbo (cl100k_base)</option>
                    <option value="gpt-3">GPT-3 Davinci/Curie (p50k_base)</option>
                    <option value="gpt-2">GPT-2 (r50k_base)</option>
                </optgroup>
                <optgroup label="Anthropic (Exact)">
                    <option value="claude">Claude (cl100k_base)</option>
                </optgroup>
                <optgroup label="Meta Llama (Template Applied)">
                    <option value="llama-3">Llama 3 / 3.1 / 3.2</option>
                    <option value="llama-2">Llama 2</option>
                </optgroup>
                <optgroup label="Chinese Models (Approximation)">
                    <option value="qwen">Qwen / Qwen2</option>
                    <option value="qwen2.5">Qwen 2.5</option>
                    <option value="glm">ChatGLM / GLM-4</option>
                    <option value="baichuan">Baichuan 2</option>
                    <option value="yi">Yi / Yi-1.5</option>
                </optgroup>
                <optgroup label="Other Models (Approximation)">
                    <option value="mistral">Mistral / Mixtral</option>
                    <option value="gemma">Gemma / Gemma 2</option>
                    <option value="phi">Phi-2 / Phi-3</option>
                    <option value="deepseek">DeepSeek</option>
                    <option value="internlm">InternLM 2</option>
                </optgroup>
            \`;
            select.value = currentTokenizer;
        }

        function switchView(view) {
            currentView = view;
            
            // Hide all views
            document.getElementById('cards-container').style.display = 'none';
            document.getElementById('table-container').style.display = 'none';
            document.getElementById('raw-container').style.display = 'none';
            
            // Remove active from all buttons
            document.getElementById('card-view-btn').classList.remove('active');
            document.getElementById('table-view-btn').classList.remove('active');
            document.getElementById('raw-view-btn').classList.remove('active');
            
            // Show selected view
            if (view === 'cards') {
                document.getElementById('cards-container').style.display = 'block';
                document.getElementById('card-view-btn').classList.add('active');
            } else if (view === 'table') {
                document.getElementById('table-container').style.display = 'block';
                document.getElementById('table-view-btn').classList.add('active');
                renderTable();
            } else if (view === 'raw') {
                document.getElementById('raw-container').style.display = 'block';
                document.getElementById('raw-view-btn').classList.add('active');
                renderRaw();
            }
        }

        function handleTokenizerChange(e) {
            currentTokenizer = e.target.value;
            // Reload data with new tokenizer
            allLines = [];
            nextOffset = 0;
            clearContainer();
            vscode.postMessage({ type: 'loadLines', offset: 0, limit: 100, searchTerm: currentSearchTerm, tokenizer: currentTokenizer });
            showLoading(true);
        }

        function openInTextEditor() {
            vscode.postMessage({ type: 'openInTextEditor' });
        }

        function performSearch() {
            const searchTerm = document.getElementById('search-input').value;
            if (searchTerm.trim()) {
                currentSearchTerm = searchTerm;
                allLines = [];
                nextOffset = 0;
                clearContainer();
                vscode.postMessage({ type: 'loadLines', offset: 0, limit: 100, searchTerm, tokenizer: currentTokenizer });
                showLoading(true);
            }
        }

        function clearSearch() {
            currentSearchTerm = '';
            document.getElementById('search-input').value = '';
            allLines = [];
            nextOffset = 0;
            clearContainer();
            vscode.postMessage({ type: 'loadLines', offset: 0, limit: 100, tokenizer: currentTokenizer });
            showLoading(true);
        }

        function loadMore() {
            vscode.postMessage({ type: 'loadLines', offset: nextOffset, limit: 100, searchTerm: currentSearchTerm, tokenizer: currentTokenizer });
            showLoading(true);
        }

        function jumpToLine() {
            const lineNum = parseInt(document.getElementById('jump-line-input').value);
            if (!isNaN(lineNum) && lineNum >= 0) {
                allLines = [];
                nextOffset = lineNum;
                clearContainer();
                vscode.postMessage({ type: 'jumpToLine', lineNumber: lineNum, tokenizer: currentTokenizer });
                showLoading(true);
            }
        }

        function clearContainer() {
            document.getElementById('cards-container').innerHTML = '';
            document.getElementById('table-body').innerHTML = '';
            document.getElementById('table-head').innerHTML = '';
            document.getElementById('raw-container').innerHTML = '';
        }

        function showLoading(show) {
            document.getElementById('loading').style.display = show ? 'block' : 'none';
            document.getElementById('load-more-container').style.display = 'none';
        }

        // Handle messages from extension - make it available globally
        window.handleMessage = function(message) {
            switch (message.type) {
                case 'clear':
                    // Reset UI state when reusing the same webview for a new file
                    fileInfo = null;
                    allLines = [];
                    nextOffset = 0;
                    hasMore = false;
                    tokenCounts = {};
                    currentSearchTerm = '';
                    clearContainer();
                    showLoading(true);
                    document.getElementById('load-more-container').style.display = 'none';
                    // Best-effort clear of header info
                    const fileNameEl = document.getElementById('file-name');
                    const fileSizeEl = document.getElementById('file-size');
                    if (fileNameEl) fileNameEl.textContent = '';
                    if (fileSizeEl) fileSizeEl.textContent = '';
                    break;

                case 'fileInfo':
                    const fileInfoTime = performance.now();
                    performance.mark('file-info-received');
                    fileInfo = message;
                    document.getElementById('file-name').textContent = message.fileName;
                    document.getElementById('file-size').textContent = \`(\${message.fileSizeMB} MB)\`;
                    
                    // Calculate actual message delay if backend timestamp provided
                    if (message.backendTimestamp) {
                        const frontendReceiveTime = Date.now();
                        const messageDelay = frontendReceiveTime - message.backendTimestamp;
                        console.log('[PERF] File info received (relative to webview load):', fileInfoTime.toFixed(2), 'ms');
                        console.log('[PERF] Backend sent at:', message.backendTimeSinceStart, 'ms after click');
                        console.log('[PERF] Message delay (backend send → frontend receive):', messageDelay.toFixed(2), 'ms');
                        console.log('[PERF] Webview initialization overhead:', (fileInfoTime - (message.backendTimeSinceStart || 0)).toFixed(2), 'ms');
                    } else {
                        console.log('[PERF] File info received (relative to webview load):', fileInfoTime.toFixed(2), 'ms');
                    }
                    break;
                    
                case 'lines':
                    const linesReceivedTime = performance.now();
                    const linesReceivedTimestamp = Date.now();
                    performance.mark('lines-received');
                    
                    // Calculate message delay if backend timestamp provided
                    if (message.backendTimestamp) {
                        const messageDelay = linesReceivedTimestamp - message.backendTimestamp;
                        console.log('[PERF] Lines message delay (backend send → frontend receive):', messageDelay.toFixed(2), 'ms');
                    }
                    
                    showLoading(false);
                    const renderStartTime = performance.now();
                    allLines = allLines.concat(message.lines);
                    nextOffset = message.nextOffset;
                    hasMore = message.hasMore;
                    
                    if (currentView === 'cards') {
                        renderCards(message.lines);
                    } else if (currentView === 'table') {
                        renderTable();
                    } else if (currentView === 'raw') {
                        renderRaw();
                    }
                    
                    const renderEndTime = performance.now();
                    const renderDuration = renderEndTime - renderStartTime;
                    updateStats();
                    
                    if (hasMore) {
                        document.getElementById('load-more-container').style.display = 'block';
                    }
                    
                    // Measure DOM render time (wait for next frame to ensure paint)
                    requestAnimationFrame(() => {
                        requestAnimationFrame(() => {
                            const paintTime = performance.now();
                            performance.mark('dom-rendered');
                            const paintDuration = paintTime - renderEndTime;
                            const totalRenderTime = paintTime - renderStartTime;
                            
                            // Initialize event listeners after first render (deferred for performance)
                            initializeEventListeners();
                            
                            // Calculate total time from fileInfo if available
                            const fileInfoMark = performance.getEntriesByName('file-info-received', 'mark')[0];
                            let totalTimeFromFileInfo = null;
                            if (fileInfoMark) {
                                totalTimeFromFileInfo = paintTime - fileInfoMark.startTime;
                                performance.measure('total-load-time', 'file-info-received', 'dom-rendered');
                            }
                            
                            // Measure render time
                            performance.measure('render-time', 'lines-received', 'dom-rendered');
                            const renderMeasure = performance.getEntriesByName('render-time', 'measure')[0];
                            
                            // Log all timing information
                            console.log('[PERF] ===== Frontend Timing =====');
                            console.log('[PERF] Lines received (relative to webview load):', linesReceivedTime.toFixed(2), 'ms');
                            console.log('[PERF] DOM construction time:', renderDuration.toFixed(2), 'ms');
                            console.log('[PERF] Paint wait time:', paintDuration.toFixed(2), 'ms');
                            console.log('[PERF] Total render time (construct + paint):', totalRenderTime.toFixed(2), 'ms');
                            if (renderMeasure) {
                                console.log('[PERF] Total time (lines received → painted):', renderMeasure.duration.toFixed(2), 'ms');
                            }
                            if (totalTimeFromFileInfo !== null) {
                                console.log('[PERF] Total time (fileInfo → painted):', totalTimeFromFileInfo.toFixed(2), 'ms');
                            }
                            console.log('[PERF] ============================');
                        });
                    });
                    break;
                    
                case 'tokens':
                    const tokensReceivedTime = performance.now();
                    performance.mark('tokens-received');
                    
                    const tokenUpdateStart = performance.now();
                    // Update token counts asynchronously
                    for (const [lineIndex, count] of Object.entries(message.tokens)) {
                        const idx = parseInt(lineIndex);
                        tokenCounts.set(idx, count);
                        
                        // Update card view
                        const cardTokenEl = document.getElementById(\`tokens-\${idx}\`);
                        if (cardTokenEl) {
                            cardTokenEl.textContent = \`\${count.toLocaleString()} tokens\`;
                        }
                        
                        // Update table view
                        const tableCellEl = document.getElementById(\`tokens-cell-\${idx}\`);
                        if (tableCellEl) {
                            tableCellEl.textContent = count.toLocaleString();
                        }
                    }
                    const tokenUpdateEnd = performance.now();
                    updateStats();
                    
                    console.log('[PERF] Tokens received (relative to webview load):', tokensReceivedTime.toFixed(2), 'ms');
                    console.log('[PERF] Token counts updated in:', (tokenUpdateEnd - tokenUpdateStart).toFixed(2), 'ms');
                    break;
                    
                case 'error':
                    showLoading(false);
                    alert(message.message);
                    break;
            }
        };
        
        // Mark handler as ready and process any queued messages
        messageHandlerReady = true;
        messageQueue.forEach(msg => window.handleMessage(msg));
        messageQueue = [];

        function renderCards(lines) {
            const container = document.getElementById('cards-container');
            
            lines.forEach(line => {
                const card = document.createElement('div');
                card.className = line.error ? 'card card-error' : 'card';
                
                const header = document.createElement('div');
                header.className = 'card-header';
                
                const title = document.createElement('div');
                title.className = 'card-title';
                title.textContent = \`Line \${line.index}\`;
                
                const tokensSpan = document.createElement('span');
                tokensSpan.className = 'card-tokens';
                tokensSpan.id = \`tokens-\${line.index}\`;
                
                // Tokens calculated asynchronously
                const tokenCount = line.tokens || tokenCounts.get(line.index);
                if (tokenCount !== undefined) {
                    tokensSpan.textContent = \`\${tokenCount.toLocaleString()} tokens\`;
                } else {
                    tokensSpan.textContent = '...';
                }
                
                header.appendChild(title);
                header.appendChild(tokensSpan);
                
                const content = document.createElement('div');
                content.className = 'card-content';
                
                if (line.error) {
                    const errorMsg = document.createElement('div');
                    errorMsg.className = 'error-message';
                    errorMsg.textContent = '⚠️ Malformed JSON';
                    content.appendChild(errorMsg);
                    content.appendChild(document.createTextNode(line.raw));
                } else {
                    content.innerHTML = syntaxHighlight(line.data);
                }
                
                card.appendChild(header);
                card.appendChild(content);
                container.appendChild(card);
            });
        }

        function renderTable() {
            if (allLines.length === 0) return;
            
            const thead = document.getElementById('table-head');
            const tbody = document.getElementById('table-body');
            
            // Extract unique columns from all loaded lines
            const columns = new Set(['_line', '_tokens']);
            allLines.forEach(line => {
                if (line.data && typeof line.data === 'object') {
                    Object.keys(line.data).forEach(key => columns.add(key));
                }
            });
            
            const columnArray = Array.from(columns);
            
            // ALWAYS clear and rebuild both header and body for clean render
            thead.innerHTML = '';
            tbody.innerHTML = '';
            
            // Create header
            const headerRow = document.createElement('tr');
            columnArray.forEach(col => {
                const th = document.createElement('th');
                if (col === '_line') {
                    th.textContent = 'Line';
                    th.className = 'line-number-col';
                } else if (col === '_tokens') {
                    th.textContent = 'Tokens';
                    th.className = 'tokens-col';
                } else {
                    th.textContent = col;
                }
                headerRow.appendChild(th);
            });
            thead.appendChild(headerRow);
            
            // Render all rows (always rebuild completely)
            allLines.forEach(line => {
                const tr = document.createElement('tr');
                
                columnArray.forEach(col => {
                    const td = document.createElement('td');
                    
                    if (col === '_line') {
                        td.textContent = line.index;
                        td.className = 'line-number-col';
                    } else if (col === '_tokens') {
                        td.className = 'tokens-col';
                        td.id = \`tokens-cell-\${line.index}\`;
                        const count = line.tokens || tokenCounts.get(line.index);
                        if (count !== undefined) {
                            td.textContent = count.toLocaleString();
                        } else {
                            td.textContent = '...';
                        }
                    } else if (line.data && line.data[col] !== undefined) {
                        const value = line.data[col];
                        if (typeof value === 'object') {
                            td.textContent = JSON.stringify(value);
                            td.title = JSON.stringify(value, null, 2);
                        } else {
                            td.textContent = String(value);
                            td.title = String(value);
                        }
                    } else {
                        td.textContent = '';
                    }
                    
                    tr.appendChild(td);
                });
                
                tbody.appendChild(tr);
            });
        }

        function syntaxHighlight(obj) {
            let json = JSON.stringify(obj, null, 2);
            json = json.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
            return json.replace(/("(\\u[a-zA-Z0-9]{4}|\\[^u]|[^\\"])*"(\s*:)?|\b(true|false|null)\b|-?\d+(?:\.\d*)?(?:[eE][+\-]?\d+)?)/g, function (match) {
                let cls = 'json-number';
                if (/^"/.test(match)) {
                    if (/:$/.test(match)) {
                        cls = 'json-key';
                    } else {
                        cls = 'json-string';
                    }
                } else if (/true|false/.test(match)) {
                    cls = 'json-boolean';
                } else if (/null/.test(match)) {
                    cls = 'json-null';
                }
                return '<span class="' + cls + '">' + match + '</span>';
            });
        }

        function renderRaw() {
            const container = document.getElementById('raw-container');
            
            // Only render new lines (incremental rendering for performance)
            const existingLines = container.children.length;
            allLines.slice(existingLines).forEach(line => {
                const lineDiv = document.createElement('div');
                lineDiv.className = 'raw-line';
                
                const lineNum = document.createElement('span');
                lineNum.className = 'raw-line-number';
                lineNum.textContent = line.index;
                
                const content = document.createElement('span');
                content.className = 'raw-line-content';
                content.textContent = line.raw;
                
                lineDiv.appendChild(lineNum);
                lineDiv.appendChild(content);
                container.appendChild(lineDiv);
            });
        }

        function updateStats() {
            document.getElementById('loaded-count').textContent = allLines.length.toLocaleString();
            
            const counts = Array.from(tokenCounts.values());
            if (counts.length > 0) {
                const avg = Math.round(counts.reduce((a, b) => a + b, 0) / counts.length);
                const max = Math.max(...counts);
                document.getElementById('avg-tokens').textContent = avg.toLocaleString();
                document.getElementById('max-tokens').textContent = max.toLocaleString();
            }
        }
    </script>
</body>
</html>`;
    }
}
