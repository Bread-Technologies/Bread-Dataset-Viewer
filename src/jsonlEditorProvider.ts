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
            localResourceRoots: [
                vscode.Uri.file(this.context.extensionPath),
            ],
        };

        console.log(`[PERF] Options set: ${Date.now() - startTime}ms`);
        
        webviewPanel.webview.html = this.getHtmlForWebview(webviewPanel.webview);
        
        console.log(`[PERF] HTML set: ${Date.now() - startTime}ms`);

        // Get file stats
        const stats = await fs.promises.stat(document.uri.fsPath);
        const fileSizeBytes = stats.size;
        const fileSizeMB = (fileSizeBytes / 1024 / 1024).toFixed(2);

        console.log(`[PERF] Stats read: ${Date.now() - startTime}ms`);
        
        // Send initial file info
        webviewPanel.webview.postMessage({
            type: 'fileInfo',
            filePath: document.uri.fsPath,
            fileName: path.basename(document.uri.fsPath),
            fileSize: fileSizeBytes,
            fileSizeMB: fileSizeMB,
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
        limit: number = 100,
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
            webview.postMessage({
                type: 'lines',
                lines,
                hasMore: lines.length === limit,
                nextOffset: lineNum,
                searchTerm,
                skippedBySearch,
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
        const markdownItUri = webview.asWebviewUri(
            vscode.Uri.file(path.join(this.context.extensionPath, 'node_modules', 'markdown-it', 'dist', 'markdown-it.min.js'))
        );
        const katexCssUri = webview.asWebviewUri(
            vscode.Uri.file(path.join(this.context.extensionPath, 'node_modules', 'katex', 'dist', 'katex.min.css'))
        );
        const katexJsUri = webview.asWebviewUri(
            vscode.Uri.file(path.join(this.context.extensionPath, 'node_modules', 'katex', 'dist', 'katex.min.js'))
        );
        const katexAutoRenderUri = webview.asWebviewUri(
            vscode.Uri.file(path.join(this.context.extensionPath, 'node_modules', 'katex', 'dist', 'contrib', 'auto-render.min.js'))
        );
        const breadIconUri = webview.asWebviewUri(
            vscode.Uri.file(path.join(this.context.extensionPath, 'icons', 'bread_alpha.png'))
        );
        return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>JSONL Viewer</title>
    <link rel="stylesheet" href="${katexCssUri}">
    <script src="${markdownItUri}"></script>
    <script src="${katexJsUri}"></script>
    <script src="${katexAutoRenderUri}"></script>
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
            padding: 4px 12px;
            cursor: pointer;
            border-radius: 5px;
            font-size: 13px;
            transition: background-color 0.2s;
            font-weight: 500;
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
            border-radius: 5px;
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
            box-shadow: 0 1px 3px rgba(0, 0, 0, 0.1);
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
            color: var(--vscode-descriptionForeground);
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

        .json-tree {
            font-family: var(--vscode-editor-font-family);
            font-size: 13px;
            line-height: 1.6;
        }

        .json-details {
            margin: 2px 0;
        }

        .json-summary {
            cursor: pointer;
        }

        .json-summary::-webkit-details-marker {
            color: var(--vscode-descriptionForeground);
        }

        .json-line {
            margin: 2px 0;
        }

        .json-index {
            color: var(--vscode-descriptionForeground);
        }

        .json-brace {
            color: var(--vscode-foreground);
        }

        .json-meta {
            color: var(--vscode-descriptionForeground);
            font-size: 11px;
            margin-left: 6px;
        }

        .json-placeholder {
            color: var(--vscode-descriptionForeground);
            font-size: 12px;
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

        .bread-icon {
            width: 18px;
            height: 18px;
            margin-right: 10px;
            vertical-align: middle;
            opacity: 0.75;
            filter: saturate(1.0) drop-shadow(0 2px 8px rgba(0, 0, 0, 0.6));
        }

        .no-results {
            text-align: center;
            padding: 48px 24px;
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

        #path-panel {
            display: none;
            position: absolute;
            top: 100%;
            left: 0;
            margin-top: 4px;
            border: 1px solid var(--vscode-panel-border);
            background-color: var(--vscode-editor-background);
            padding: 8px;
            border-radius: 5px;
            box-shadow: 0 4px 12px rgba(0, 0, 0, 0.3);
            z-index: 1000;
            min-width: 300px;
            max-width: 400px;
        }

        .path-panel-header {
            display: flex;
            justify-content: space-between;
            align-items: center;
            margin-bottom: 8px;
            font-size: 12px;
            color: var(--vscode-descriptionForeground);
        }

        .path-panel-actions {
            display: flex;
            gap: 8px;
            margin-bottom: 8px;
        }

        .path-panel-list {
            max-height: 220px;
            overflow: auto;
            border: 1px solid var(--vscode-panel-border);
            padding: 6px 8px;
            border-radius: 4px;
        }

        .path-item {
            display: flex;
            gap: 8px;
            align-items: center;
            font-family: var(--vscode-editor-font-family);
            font-size: 12px;
            padding: 2px 0;
            cursor: pointer;
        }
        
        .path-item:hover {
            background-color: var(--vscode-list-hoverBackground);
        }

        .path-empty {
            color: var(--vscode-descriptionForeground);
            font-size: 12px;
            padding: 6px 0;
        }

        .chat-thread {
            display: flex;
            flex-direction: column;
            gap: 10px;
        }

        .chat-bubble {
            border: 1.5px solid var(--vscode-panel-border);
            border-radius: 10px;
            padding: 16px 20px;
            max-width: 900px;
            background-color: var(--vscode-editor-background);
            box-shadow: 0 2px 4px rgba(0, 0, 0, 0.1);
        }

        .chat-bubble.user {
            align-self: flex-end;
            background-color: var(--vscode-editorWidget-background);
        }

        .chat-bubble.assistant {
            align-self: flex-start;
        }

        .chat-bubble.system {
            align-self: stretch;
            background-color: var(--vscode-inputValidation-infoBackground);
        }

        .chat-bubble.tool {
            align-self: stretch;
            background-color: var(--vscode-inputValidation-warningBackground);
        }

        .chat-role {
            font-size: 11px;
            color: var(--vscode-descriptionForeground);
            margin-bottom: 12px;
            text-transform: uppercase;
            letter-spacing: 0.03em;
        }

        .chat-content {
            padding: 4px;
            line-height: 1.9;
        }

        .chat-content p {
            margin: 0 0 10px 0;
        }

        .chat-content p:last-child {
            margin-bottom: 0;
        }

        .chat-content h1,
        .chat-content h2,
        .chat-content h3,
        .chat-content h4,
        .chat-content h5,
        .chat-content h6 {
            margin: 12px 0 8px 0;
            line-height: 1.3;
        }

        .chat-content h1:first-child,
        .chat-content h2:first-child,
        .chat-content h3:first-child,
        .chat-content h4:first-child,
        .chat-content h5:first-child,
        .chat-content h6:first-child {
            margin-top: 0;
        }

        .chat-content ul,
        .chat-content ol {
            margin: 8px 0;
            padding-left: 24px;
        }

        .chat-content li {
            margin: 4px 0;
        }

        .chat-content code {
            font-family: var(--vscode-editor-font-family);
            background-color: var(--vscode-textCodeBlock-background);
            padding: 0 4px;
            border-radius: 3px;
        }

        .chat-content pre {
            margin: 8px 0;
        }

        .chat-content pre code {
            display: block;
            padding: 12px;
            background-color: var(--vscode-textCodeBlock-background);
            border-radius: 6px;
            overflow-x: auto;
        }

    </style>
</head>
<body>
    <div id="toolbar">
        <div class="toolbar-section">
            <img src="${breadIconUri}" alt="🍞" class="bread-icon" title="ML Workbench JSONL Viewer">
            <strong id="file-name"></strong>
            <span style="font-size: 11px; color: var(--vscode-descriptionForeground);" id="file-size"></span>
        </div>
        
        <div class="toolbar-divider"></div>
        
        <div class="toolbar-section">
            <button id="pretty-view-btn" class="secondary active">Pretty</button>
            <button id="render-view-btn" class="secondary">Render</button>
            <button id="table-view-btn" class="secondary">Table</button>
            <button id="raw-view-btn" class="secondary">Raw</button>
        </div>

        <div class="toolbar-divider"></div>

        <div class="toolbar-section" style="position: relative;">
            <button id="path-toggle-btn" class="secondary">Filter <span style="font-size: 10px; margin-left: 2px; vertical-align: middle;">▾</span></button>
            <div id="path-panel">
                <div class="path-panel-header">
                    <strong>Filter</strong>
                    <span id="path-count">0/0 selected</span>
                </div>
                <div class="path-panel-actions">
                    <button id="path-select-all" class="secondary">Select All</button>
                    <button id="path-clear" class="secondary">Clear</button>
                </div>
                <div class="path-panel-list" id="path-list"></div>
            </div>
        </div>
        
        <div class="toolbar-divider"></div>
        
        <div class="toolbar-section">
            <button id="edit-btn" class="secondary">Edit in Text Editor</button>
        </div>
        
        <div class="toolbar-divider"></div>
        
        <div class="toolbar-section">
            <label for="tokenizer-select" style="font-size: 12px; margin-right: 4px;" title="Select model tokenizer. For chat completions format, applies model-specific chat template before counting tokens.">Tokenizer:</label>
            <select id="tokenizer-select" title="OpenAI models use exact tokenizers. Other models use approximations with chat templates applied for chat completions format.">
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
            </select>
        </div>
        
        <div class="toolbar-divider"></div>
        
        <div class="toolbar-section">
            <input type="text" id="search-input" placeholder="Search records...">
            <button id="search-btn" class="secondary">Search</button>
            <button id="clear-search-btn" class="secondary">Clear</button>
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
        <div id="pretty-container"></div>
        <div id="render-container" style="display: none;"></div>
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
        const vscode = acquireVsCodeApi();
        
        let allLines = [];
        let nextOffset = 0;
        let hasMore = false;
        let currentView = 'pretty';
        let currentSearchTerm = '';
        let fileInfo = null;
        let tokenCounts = new Map();
        let currentTokenizer = 'gpt-4';

        const MAX_PATHS = 2000;
        const MAX_PATH_DEPTH = 8;
        const MAX_ARRAY_SCAN = 20;
        const AUTO_EXPAND_LIMIT = 50;
        let availablePaths = new Set();
        let selectedPaths = new Set();
        let pathLimitReached = false;
        let pathPanelVisible = false;
        
        // Initialize
        document.getElementById('pretty-view-btn').addEventListener('click', () => switchView('pretty'));
        document.getElementById('render-view-btn').addEventListener('click', () => switchView('render'));
        document.getElementById('table-view-btn').addEventListener('click', () => switchView('table'));
        document.getElementById('raw-view-btn').addEventListener('click', () => switchView('raw'));
        document.getElementById('search-btn').addEventListener('click', performSearch);
        document.getElementById('clear-search-btn').addEventListener('click', clearSearch);
        document.getElementById('load-more-btn').addEventListener('click', loadMore);
        document.getElementById('jump-btn').addEventListener('click', jumpToLine);
        document.getElementById('tokenizer-select').addEventListener('change', handleTokenizerChange);
        document.getElementById('edit-btn').addEventListener('click', openInTextEditor);
        document.getElementById('path-toggle-btn').addEventListener('click', togglePathPanel);
        document.getElementById('path-select-all').addEventListener('click', selectAllPaths);
        document.getElementById('path-clear').addEventListener('click', clearSelectedPaths);
        
        document.getElementById('search-input').addEventListener('keypress', (e) => {
            if (e.key === 'Enter') performSearch();
        });
        
        document.getElementById('jump-line-input').addEventListener('keypress', (e) => {
            if (e.key === 'Enter') jumpToLine();
        });

        function switchView(view) {
            currentView = view;
            
            // Hide all views
            document.getElementById('pretty-container').style.display = 'none';
            document.getElementById('render-container').style.display = 'none';
            document.getElementById('table-container').style.display = 'none';
            document.getElementById('raw-container').style.display = 'none';
            
            // Remove active from all buttons
            document.getElementById('pretty-view-btn').classList.remove('active');
            document.getElementById('render-view-btn').classList.remove('active');
            document.getElementById('table-view-btn').classList.remove('active');
            document.getElementById('raw-view-btn').classList.remove('active');
            
            // Show selected view
            if (view === 'pretty') {
                document.getElementById('pretty-container').style.display = 'block';
                document.getElementById('pretty-view-btn').classList.add('active');
                renderPretty(allLines, true);
            } else if (view === 'render') {
                document.getElementById('render-container').style.display = 'block';
                document.getElementById('render-view-btn').classList.add('active');
                renderChat(allLines, true);
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
            resetAvailablePaths();
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
                resetAvailablePaths();
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
            resetAvailablePaths();
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
                resetAvailablePaths();
                clearContainer();
                vscode.postMessage({ type: 'jumpToLine', lineNumber: lineNum, tokenizer: currentTokenizer });
                showLoading(true);
            }
        }

        function clearContainer() {
            document.getElementById('pretty-container').innerHTML = '';
            document.getElementById('render-container').innerHTML = '';
            document.getElementById('table-body').innerHTML = '';
            document.getElementById('table-head').innerHTML = '';
            document.getElementById('raw-container').innerHTML = '';
        }

        function resetAvailablePaths() {
            availablePaths = new Set();
            pathLimitReached = false;
            if (pathPanelVisible) {
                renderPathList();
            }
        }

        function showLoading(show) {
            document.getElementById('loading').style.display = show ? 'block' : 'none';
            document.getElementById('load-more-container').style.display = 'none';
        }

        // Handle messages from extension
        window.addEventListener('message', event => {
            const message = event.data;
            
            switch (message.type) {
                case 'fileInfo':
                    fileInfo = message;
                    document.getElementById('file-name').textContent = message.fileName;
                    document.getElementById('file-size').textContent = \`(\${message.fileSizeMB} MB)\`;
                    break;
                    
                case 'lines':
                    showLoading(false);
                    allLines = allLines.concat(message.lines);
                    nextOffset = message.nextOffset;
                    hasMore = message.hasMore;

                    updatePathsFromLines(message.lines);
                    
                    if (currentView === 'pretty') {
                        renderPretty(message.lines);
                    } else if (currentView === 'render') {
                        renderChat(message.lines);
                    } else if (currentView === 'table') {
                        renderTable();
                    } else if (currentView === 'raw') {
                        renderRaw();
                    }
                    
                    updateStats();
                    
                    if (hasMore) {
                        document.getElementById('load-more-container').style.display = 'block';
                    }
                    break;
                    
                case 'tokens':
                    // Update token counts asynchronously
                    for (const [lineIndex, count] of Object.entries(message.tokens)) {
                        const idx = parseInt(lineIndex);
                        tokenCounts.set(idx, count);
                        
                        // Update pretty view
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
                    updateStats();
                    break;
                    
                case 'error':
                    showLoading(false);
                    alert(message.message);
                    break;
            }
        });

        function togglePathPanel() {
            pathPanelVisible = !pathPanelVisible;
            const panel = document.getElementById('path-panel');
            panel.style.display = pathPanelVisible ? 'block' : 'none';
            if (pathPanelVisible) {
                renderPathList();
            }
        }

        // Close dropdown when clicking outside
        document.addEventListener('click', (e) => {
            const panel = document.getElementById('path-panel');
            const btn = document.getElementById('path-toggle-btn');
            if (pathPanelVisible && !panel.contains(e.target) && e.target !== btn) {
                pathPanelVisible = false;
                panel.style.display = 'none';
            }
        });

        function selectAllPaths() {
            selectedPaths = new Set(availablePaths);
            renderPathList();
            rerenderPretty();
            rerenderRender();
        }

        function clearSelectedPaths() {
            selectedPaths.clear();
            renderPathList();
            rerenderPretty();
            rerenderRender();
        }

        function updatePathCount(total) {
            const countEl = document.getElementById('path-count');
            const suffix = pathLimitReached ? ' (truncated)' : '';
            countEl.textContent = selectedPaths.size + '/' + total + ' selected' + suffix;
        }

        function buildPathTree(paths) {
            const tree = {};
            paths.forEach(path => {
                // Split by dots, but preserve [] notation
                const parts = path.split('.').map(p => p.trim()).filter(p => p);
                let current = tree;
                let fullPath = '';
                
                parts.forEach((part, index) => {
                    if (index > 0) fullPath += '.';
                    fullPath += part;
                    
                    if (!current[part]) {
                        current[part] = {
                            fullPath: fullPath,
                            children: {},
                            isArray: part.endsWith('[]')
                        };
                    }
                    current = current[part].children;
                });
            });
            return tree;
        }

        function getAllDescendantPaths(path) {
            const descendants = [];
            availablePaths.forEach(p => {
                if (p !== path && p.startsWith(path + '.')) {
                    descendants.push(p);
                }
            });
            return descendants;
        }

        function renderPathTree(tree, container, depth = 0) {
            const keys = Object.keys(tree).sort();
            
            keys.forEach(key => {
                const node = tree[key];
                const path = node.fullPath;
                
                const label = document.createElement('label');
                label.className = 'path-item';
                label.style.paddingLeft = (depth * 16) + 'px';

                const checkbox = document.createElement('input');
                checkbox.type = 'checkbox';
                checkbox.checked = selectedPaths.has(path);
                checkbox.addEventListener('change', (e) => {
                    e.stopPropagation();
                    
                    if (checkbox.checked) {
                        selectedPaths.add(path);
                        // Also select all descendants
                        const descendants = getAllDescendantPaths(path);
                        descendants.forEach(d => selectedPaths.add(d));
                    } else {
                        selectedPaths.delete(path);
                        // Also deselect all descendants
                        const descendants = getAllDescendantPaths(path);
                        descendants.forEach(d => selectedPaths.delete(d));
                    }
                    
                    renderPathList();
                    rerenderPretty();
                    rerenderRender();
                });

                const text = document.createElement('span');
                // Display array fields with (array) notation
                if (key.endsWith('[]')) {
                    text.textContent = key.slice(0, -2) + ' (array)';
                } else {
                    text.textContent = key;
                }

                label.appendChild(checkbox);
                label.appendChild(text);
                container.appendChild(label);
                
                // Render children
                if (Object.keys(node.children).length > 0) {
                    renderPathTree(node.children, container, depth + 1);
                }
            });
        }

        function renderPathList() {
            const list = document.getElementById('path-list');
            const paths = Array.from(new Set([...availablePaths, ...selectedPaths])).sort();
            updatePathCount(paths.length);

            list.innerHTML = '';
            if (paths.length === 0) {
                const empty = document.createElement('div');
                empty.className = 'path-empty';
                empty.textContent = 'No paths discovered yet.';
                list.appendChild(empty);
                return;
            }

            const tree = buildPathTree(paths);
            renderPathTree(tree, list);
        }

        function updatePathsFromLines(lines) {
            let added = false;
            lines.forEach(line => {
                if (line.error || line.data === null || line.data === undefined) return;
                if (collectPaths(line.data, '', 0)) {
                    added = true;
                }
            });
            if ((added || pathLimitReached) && pathPanelVisible) {
                renderPathList();
            }
        }

        function addPath(path) {
            if (!path) return false;
            if (availablePaths.has(path)) return false;
            if (availablePaths.size >= MAX_PATHS) {
                pathLimitReached = true;
                return false;
            }
            availablePaths.add(path);
            selectedPaths.add(path); // Auto-select all paths by default
            return true;
        }

        function collectPaths(value, path, depth) {
            if (pathLimitReached || depth > MAX_PATH_DEPTH) return false;
            let added = false;

            if (value === null || typeof value !== 'object') {
                if (path) {
                    added = addPath(path) || added;
                }
                return added;
            }

            if (Array.isArray(value)) {
                // Only use the array notation (path[]) to avoid duplicates
                const arrayPath = path ? path + '[]' : '[]';
                added = addPath(arrayPath) || added;
                const scanLength = Math.min(value.length, MAX_ARRAY_SCAN);
                for (let i = 0; i < scanLength; i++) {
                    added = collectPaths(value[i], arrayPath, depth + 1) || added;
                    if (pathLimitReached) break;
                }
                return added;
            }

            if (path) {
                added = addPath(path) || added;
            }

            const keys = Object.keys(value);
            for (const key of keys) {
                const childPath = path ? path + '.' + key : key;
                added = collectPaths(value[key], childPath, depth + 1) || added;
                if (pathLimitReached) break;
            }

            return added;
        }

        function filterValueForPaths(value, path) {
            if (selectedPaths.size === 0) return value;
            if (path && selectedPaths.has(path)) return value;

            if (value === null || typeof value !== 'object') {
                return selectedPaths.has(path) ? value : undefined;
            }

            if (Array.isArray(value)) {
                const arrayPath = path ? path + '[]' : '[]';
                if (selectedPaths.has(arrayPath)) return value;
                const filtered = [];
                for (let i = 0; i < value.length; i++) {
                    const item = filterValueForPaths(value[i], arrayPath);
                    if (item !== undefined) {
                        filtered.push(item);
                    }
                }
                return filtered.length ? filtered : undefined;
            }

            const result = {};
            Object.keys(value).forEach(key => {
                const childPath = path ? path + '.' + key : key;
                const childValue = filterValueForPaths(value[key], childPath);
                if (childValue !== undefined) {
                    result[key] = childValue;
                }
            });

            return Object.keys(result).length ? result : undefined;
        }

        function rerenderPretty() {
            if (currentView === 'pretty') {
                renderPretty(allLines, true);
            }
        }

        function rerenderRender() {
            if (currentView === 'render') {
                renderChat(allLines, true);
            }
        }

        function renderPretty(lines, reset = false) {
            const container = document.getElementById('pretty-container');
            if (reset) {
                container.innerHTML = '';
            }

            lines.forEach(line => {
                const card = document.createElement('div');
                card.className = line.error ? 'card card-error' : 'card';

                const header = document.createElement('div');
                header.className = 'card-header';

                const title = document.createElement('div');
                title.className = 'card-title';
                title.textContent = 'Line ' + line.index;

                const tokensSpan = document.createElement('span');
                tokensSpan.className = 'card-tokens';
                tokensSpan.id = 'tokens-' + line.index;

                const tokenCount = line.tokens || tokenCounts.get(line.index);
                if (tokenCount !== undefined) {
                    tokensSpan.textContent = tokenCount.toLocaleString() + ' tokens';
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
                    errorMsg.textContent = 'Malformed JSON';
                    content.appendChild(errorMsg);
                    content.appendChild(document.createTextNode(line.raw));
                } else {
                    const filtered = filterValueForPaths(line.data, '');
                    if (filtered === undefined) {
                        const placeholder = document.createElement('div');
                        placeholder.className = 'json-placeholder';
                        placeholder.textContent = 'No matching paths for this record.';
                        content.appendChild(placeholder);
                    } else {
                        const tree = renderJsonTree(filtered, 0, null, null);
                        if (tree) {
                            tree.classList.add('json-tree');
                            content.appendChild(tree);
                        }
                    }
                }

                card.appendChild(header);
                card.appendChild(content);
                container.appendChild(card);
            });
        }

        function renderChat(lines, reset = false) {
            const container = document.getElementById('render-container');
            if (reset) {
                container.innerHTML = '';
            }

            lines.forEach(line => {
                const card = document.createElement('div');
                card.className = line.error ? 'card card-error' : 'card';

                const header = document.createElement('div');
                header.className = 'card-header';

                const title = document.createElement('div');
                title.className = 'card-title';
                title.textContent = 'Line ' + line.index;

                const tokensSpan = document.createElement('span');
                tokensSpan.className = 'card-tokens';
                tokensSpan.id = 'tokens-' + line.index;

                const tokenCount = line.tokens || tokenCounts.get(line.index);
                if (tokenCount !== undefined) {
                    tokensSpan.textContent = tokenCount.toLocaleString() + ' tokens';
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
                    errorMsg.textContent = 'Malformed JSON';
                    content.appendChild(errorMsg);
                    content.appendChild(document.createTextNode(line.raw));
                } else {
                    const filtered = filterValueForPaths(line.data, '');
                    
                    // Check for Gemini format (text_input/output)
                    if (filtered && (filtered.text_input !== undefined || filtered.output !== undefined)) {
                        const thread = document.createElement('div');
                        thread.className = 'chat-thread';
                        const fragment = document.createDocumentFragment();

                        // Render text_input as user message
                        if (filtered.text_input !== undefined) {
                            const bubble = document.createElement('div');
                            bubble.className = 'chat-bubble user';

                            const roleLabel = document.createElement('div');
                            roleLabel.className = 'chat-role';
                            roleLabel.textContent = 'user';

                            const body = document.createElement('div');
                            body.className = 'chat-content';
                            body.innerHTML = renderMarkdown(String(filtered.text_input || ''));
                            renderLatexInElement(body);

                            bubble.appendChild(roleLabel);
                            bubble.appendChild(body);
                            fragment.appendChild(bubble);
                        }

                        // Render output as assistant message
                        if (filtered.output !== undefined) {
                            const bubble = document.createElement('div');
                            bubble.className = 'chat-bubble assistant';

                            const roleLabel = document.createElement('div');
                            roleLabel.className = 'chat-role';
                            roleLabel.textContent = 'assistant';

                            const body = document.createElement('div');
                            body.className = 'chat-content';
                            body.innerHTML = renderMarkdown(String(filtered.output || ''));
                            renderLatexInElement(body);

                            bubble.appendChild(roleLabel);
                            bubble.appendChild(body);
                            fragment.appendChild(bubble);
                        }

                        thread.appendChild(fragment);
                        content.appendChild(thread);
                    } else {
                        // Handle standard chat format (messages array)
                        const messages = filtered && filtered.messages;
                        if (!messages || !Array.isArray(messages)) {
                            const placeholder = document.createElement('div');
                            placeholder.className = 'json-placeholder';
                            placeholder.textContent = 'No matching messages for this record.';
                            content.appendChild(placeholder);
                        } else {
                            const thread = document.createElement('div');
                            thread.className = 'chat-thread';
                            const fragment = document.createDocumentFragment();

                            messages.forEach((message, idx) => {
                                const role = normalizeRole(message && message.role ? message.role : 'unknown');
                                const bubble = document.createElement('div');
                                bubble.className = 'chat-bubble ' + role;

                                const roleLabel = document.createElement('div');
                                roleLabel.className = 'chat-role';
                                roleLabel.textContent = role;

                                const body = document.createElement('div');
                                body.className = 'chat-content';
                                body.innerHTML = renderMarkdown(normalizeMessageContent(message && message.content));
                                renderLatexInElement(body);

                                bubble.appendChild(roleLabel);
                                bubble.appendChild(body);
                                fragment.appendChild(bubble);
                            });

                            thread.appendChild(fragment);
                            content.appendChild(thread);
                        }
                    }
                }

                card.appendChild(header);
                card.appendChild(content);
                container.appendChild(card);
            });
        }

        function renderJsonTree(value, depth, label, labelType) {
            if (value === null || typeof value !== 'object') {
                return renderPrimitiveLine(value, depth, label, labelType);
            }
            if (Array.isArray(value)) {
                return renderArrayNode(value, depth, label, labelType);
            }
            return renderObjectNode(value, depth, label, labelType);
        }

        function getMarkdownRenderer() {
            if (!window.markdownit) {
                return null;
            }
            if (window.__markdownRenderer) {
                return window.__markdownRenderer;
            }
            const renderer = window.markdownit({
                html: false,
                linkify: true,
                breaks: true,
            });
            window.__markdownRenderer = renderer;
            return renderer;
        }

        function renderMarkdown(text) {
            const renderer = getMarkdownRenderer();
            if (!renderer) {
            return escapeHtml(text).replace(/\\n/g, '<br>');
            }
            return renderer.render(text || '');
        }

        function renderLatexInElement(element) {
            if (typeof renderMathInElement === 'function') {
                try {
                    renderMathInElement(element, {
                        delimiters: [
                            {left: '$$', right: '$$', display: true},
                            {left: '$', right: '$', display: false},
                            {left: '\\\\[', right: '\\\\]', display: true},
                            {left: '\\\\(', right: '\\\\)', display: false}
                        ],
                        throwOnError: false
                    });
                } catch (e) {
                    console.warn('LaTeX rendering failed:', e);
                }
            }
        }

        function normalizeRole(role) {
            const normalized = String(role || 'unknown').toLowerCase();
            if (normalized === 'user' || normalized === 'assistant' || normalized === 'system' || normalized === 'tool') {
                return normalized;
            }
            return 'assistant';
        }

        function normalizeMessageContent(content) {
            if (content === null || content === undefined) {
                return '';
            }
            if (Array.isArray(content)) {
                const parts = [];
                content.forEach(part => {
                    if (typeof part === 'string') {
                        parts.push(part);
                        return;
                    }
                    if (part && typeof part === 'object') {
                        if (part.type === 'text' && typeof part.text === 'string') {
                            parts.push(part.text);
                        } else if (part.type === 'input_text' && typeof part.text === 'string') {
                            parts.push(part.text);
                        } else if (part.type === 'image_url' && part.image_url && part.image_url.url) {
                            parts.push('[image] ' + part.image_url.url);
                        } else {
                            parts.push(JSON.stringify(part));
                        }
                        return;
                    }
                    parts.push(String(part));
                });
                return parts.join('\\n');
            }
            if (typeof content === 'string') {
                return content;
            }
            return JSON.stringify(content, null, 2);
        }

        function escapeHtml(value) {
            return String(value || '')
                .replace(/&/g, '&amp;')
                .replace(/</g, '&lt;')
                .replace(/>/g, '&gt;')
                .replace(/"/g, '&quot;')
                .replace(/'/g, '&#39;');
        }

        function renderPrimitiveLine(value, depth, label, labelType) {
            const line = document.createElement('div');
            line.className = 'json-line';
            line.style.marginLeft = (depth * 16) + 'px';

            if (label !== null && label !== undefined) {
                appendLabel(line, label, labelType);
            }

            const valueSpan = createValueSpan(value);
            line.appendChild(valueSpan);
            return line;
        }

        function renderObjectNode(obj, depth, label, labelType) {
            const keys = Object.keys(obj);
            if (keys.length === 0) {
                return renderEmptyContainer('{}', depth, label, labelType);
            }

            const details = document.createElement('details');
            details.className = 'json-details';
            details.open = keys.length <= AUTO_EXPAND_LIMIT;
            details.style.marginLeft = (depth * 16) + 'px';

            const summary = document.createElement('summary');
            summary.className = 'json-summary';
            if (label !== null && label !== undefined) {
                appendLabel(summary, label, labelType);
            }
            summary.appendChild(createBraceSpan('{'));
            const meta = document.createElement('span');
            meta.className = 'json-meta';
            meta.textContent = keys.length + ' keys';
            summary.appendChild(meta);
            summary.appendChild(createBraceSpan('}'));
            details.appendChild(summary);

            const renderChildren = () => {
                if (details.dataset.rendered === 'true') return;
                details.dataset.rendered = 'true';
                keys.forEach(key => {
                    const child = renderJsonTree(obj[key], depth + 1, key, 'key');
                    if (child) {
                        details.appendChild(child);
                    }
                });
                details.appendChild(renderClosingBrace('}', depth));
            };

            if (details.open) {
                renderChildren();
            }
            details.addEventListener('toggle', () => {
                if (details.open) {
                    renderChildren();
                }
            });

            return details;
        }

        function renderArrayNode(arr, depth, label, labelType) {
            if (arr.length === 0) {
                return renderEmptyContainer('[]', depth, label, labelType);
            }

            const details = document.createElement('details');
            details.className = 'json-details';
            details.open = arr.length <= AUTO_EXPAND_LIMIT;
            details.style.marginLeft = (depth * 16) + 'px';

            const summary = document.createElement('summary');
            summary.className = 'json-summary';
            if (label !== null && label !== undefined) {
                appendLabel(summary, label, labelType);
            }
            summary.appendChild(createBraceSpan('['));
            const meta = document.createElement('span');
            meta.className = 'json-meta';
            meta.textContent = arr.length + ' items';
            summary.appendChild(meta);
            summary.appendChild(createBraceSpan(']'));
            details.appendChild(summary);

            const renderChildren = () => {
                if (details.dataset.rendered === 'true') return;
                details.dataset.rendered = 'true';
                arr.forEach((item, index) => {
                    const child = renderJsonTree(item, depth + 1, '[' + index + ']', 'index');
                    if (child) {
                        details.appendChild(child);
                    }
                });
                details.appendChild(renderClosingBrace(']', depth));
            };

            if (details.open) {
                renderChildren();
            }
            details.addEventListener('toggle', () => {
                if (details.open) {
                    renderChildren();
                }
            });

            return details;
        }

        function renderEmptyContainer(braces, depth, label, labelType) {
            const line = document.createElement('div');
            line.className = 'json-line';
            line.style.marginLeft = (depth * 16) + 'px';

            if (label !== null && label !== undefined) {
                appendLabel(line, label, labelType);
            }
            line.appendChild(createBraceSpan(braces));
            return line;
        }

        function renderClosingBrace(brace, depth) {
            const line = document.createElement('div');
            line.className = 'json-line';
            line.style.marginLeft = (depth * 16) + 'px';
            line.appendChild(createBraceSpan(brace));
            return line;
        }

        function appendLabel(container, label, labelType) {
            const labelSpan = document.createElement('span');
            if (labelType === 'index') {
                labelSpan.className = 'json-index';
                labelSpan.textContent = label;
            } else {
                labelSpan.className = 'json-key';
                labelSpan.textContent = '\"' + label + '\"';
            }
            container.appendChild(labelSpan);
            container.appendChild(document.createTextNode(': '));
        }

        function createValueSpan(value) {
            const span = document.createElement('span');
            if (value === null) {
                span.className = 'json-null';
                span.textContent = 'null';
                return span;
            }
            const type = typeof value;
            if (type === 'string') {
                span.className = 'json-string';
                span.textContent = JSON.stringify(value);
            } else if (type === 'number') {
                span.className = 'json-number';
                span.textContent = String(value);
            } else if (type === 'boolean') {
                span.className = 'json-boolean';
                span.textContent = value ? 'true' : 'false';
            } else {
                span.className = 'json-string';
                span.textContent = JSON.stringify(value);
            }
            return span;
        }

        function createBraceSpan(char) {
            const span = document.createElement('span');
            span.className = 'json-brace';
            span.textContent = char;
            return span;
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
