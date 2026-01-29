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
                        message.tokenizer,
                        message.tokenMode
                    );
                    break;
                case 'jumpToLine':
                    await this.jumpToLine(
                        document.uri.fsPath,
                        webviewPanel.webview,
                        message.lineNumber,
                        message.tokenizer,
                        message.tokenMode
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
        tokenizer: string = 'qwen-3',
        tokenMode: string = 'auto'
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
            setImmediate(async () => {
                const tokenStart = Date.now();
                const tokensMap: { [key: number]: any } = {};
                const errors: string[] = [];

                for (const line of lines) {
                    try {
                        const result = await countTokens(line.raw, tokenizer, tokenMode);
                        tokensMap[line.index] = {
                            count: result.count,
                            mode: result.mode,
                            key: result.key,
                            preview: result.preview,
                        };
                    } catch (error) {
                        const errorMsg = String(error);
                        console.error(`Error counting tokens for line ${line.index}:`, error);
                        tokensMap[line.index] = {
                            count: 0,
                            mode: 'error',
                            error: errorMsg,
                        };
                        if (!errors.some(e => e === errorMsg)) {
                            errors.push(errorMsg);
                        }
                    }
                }
                console.log(`[PERF] Token counting done: ${Date.now() - tokenStart}ms for ${lines.length} lines`);

                webview.postMessage({
                    type: 'tokens',
                    tokens: tokensMap,
                });

                // Send errors if any
                if (errors.length > 0) {
                    webview.postMessage({
                        type: 'tokenErrors',
                        errors: errors
                    });
                }

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
        tokenizer: string = 'qwen-3',
        tokenMode: string = 'auto'
    ): Promise<void> {
        // For jump-to-line, we load from that line
        await this.loadLines(filePath, webview, targetLine, 100, undefined, tokenizer, tokenMode);
    }

    private getHtmlForWebview(webview: vscode.Webview): string {
        // Generate URIs for external resources
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

        // Generate URIs for webview resources
        const mainCssUri = webview.asWebviewUri(
            vscode.Uri.file(path.join(this.context.extensionPath, 'src', 'webview', 'styles', 'main.css'))
        );
        const viewerJsUri = webview.asWebviewUri(
            vscode.Uri.file(path.join(this.context.extensionPath, 'src', 'webview', 'scripts', 'viewer.js'))
        );

        // Load HTML template
        const htmlPath = path.join(this.context.extensionPath, 'src', 'webview', 'html', 'dataViewer.html');
        let html = fs.readFileSync(htmlPath, 'utf8');

        // Inject URIs into template
        html = html.replace(/\{\{katexCssUri\}\}/g, katexCssUri.toString());
        html = html.replace(/\{\{markdownItUri\}\}/g, markdownItUri.toString());
        html = html.replace(/\{\{katexJsUri\}\}/g, katexJsUri.toString());
        html = html.replace(/\{\{katexAutoRenderUri\}\}/g, katexAutoRenderUri.toString());
        html = html.replace(/\{\{breadIconUri\}\}/g, breadIconUri.toString());
        html = html.replace(/\{\{mainCssUri\}\}/g, mainCssUri.toString());
        html = html.replace(/\{\{viewerJsUri\}\}/g, viewerJsUri.toString());

        return html;
    }
}
