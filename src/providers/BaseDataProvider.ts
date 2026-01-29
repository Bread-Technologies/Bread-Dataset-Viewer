import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { IDataLoader, FileFormat } from '../formats/interfaces';
import { countTokens } from '../utils/tokenizer';
import { LoadLinesMessage, JumpToLineMessage } from '../webview/types/messages';

/**
 * Abstract base provider for data file viewers
 * Provides common logic for document lifecycle, webview setup, and data loading
 */
export abstract class BaseDataProvider implements vscode.CustomReadonlyEditorProvider {
    constructor(
        protected readonly context: vscode.ExtensionContext,
        protected readonly supportedFormats: FileFormat[]
    ) {}

    /**
     * Create a format-specific data loader
     * Subclasses must implement this to return the appropriate loader
     */
    abstract createLoader(filePath: string): IDataLoader;

    /**
     * Open custom document (standard lifecycle)
     */
    async openCustomDocument(
        uri: vscode.Uri,
        openContext: vscode.CustomDocumentOpenContext,
        token: vscode.CancellationToken
    ): Promise<vscode.CustomDocument> {
        return { uri, dispose: () => {} };
    }

    /**
     * Resolve custom editor - setup webview and initialize loader
     */
    async resolveCustomEditor(
        document: vscode.CustomDocument,
        webviewPanel: vscode.WebviewPanel,
        token: vscode.CancellationToken
    ): Promise<void> {
        const startTime = Date.now();

        // Setup webview options
        webviewPanel.webview.options = {
            enableScripts: true,
            localResourceRoots: [
                vscode.Uri.file(this.context.extensionPath),
            ],
        };

        console.log(`[PERF] Options set: ${Date.now() - startTime}ms`);

        // Load HTML for webview
        webviewPanel.webview.html = this.getHtmlForWebview(webviewPanel.webview);

        console.log(`[PERF] HTML set: ${Date.now() - startTime}ms`);

        // Get file stats
        const stats = await fs.promises.stat(document.uri.fsPath);
        const fileSizeBytes = stats.size;
        const fileSizeMB = (fileSizeBytes / 1024 / 1024).toFixed(2);

        console.log(`[PERF] Stats read: ${Date.now() - startTime}ms`);

        // Initialize loader to get metadata
        const loader = this.createLoader(document.uri.fsPath);
        await loader.initialize(document.uri.fsPath);
        const metadata = await loader.getMetadata();

        console.log(`[PERF] Loader initialized: ${Date.now() - startTime}ms`);

        // Send initial file info with format and schema
        webviewPanel.webview.postMessage({
            type: 'fileInfo',
            filePath: document.uri.fsPath,
            fileName: path.basename(document.uri.fsPath),
            fileSize: fileSizeBytes,
            fileSizeMB: fileSizeMB,
            format: metadata.format,
            schema: metadata.schema,
        });

        console.log(`[PERF] File info sent: ${Date.now() - startTime}ms`);

        // Setup message handlers
        this.setupMessageHandlers(document, webviewPanel);

        // Load initial batch
        await this.loadAndSendRows(document.uri.fsPath, webviewPanel.webview, 0, 100);

        console.log(`[PERF] Initial data loaded: ${Date.now() - startTime}ms`);
    }

    /**
     * Setup message handlers for webview communication
     */
    protected setupMessageHandlers(
        document: vscode.CustomDocument,
        webviewPanel: vscode.WebviewPanel
    ): void {
        webviewPanel.webview.onDidReceiveMessage(async (message) => {
            switch (message.type) {
                case 'loadLines':
                    const loadMsg = message as LoadLinesMessage;
                    await this.loadAndSendRows(
                        document.uri.fsPath,
                        webviewPanel.webview,
                        loadMsg.offset,
                        loadMsg.limit,
                        loadMsg.searchTerm,
                        loadMsg.tokenizer
                    );
                    break;
                case 'jumpToLine':
                    const jumpMsg = message as JumpToLineMessage;
                    await this.jumpToRow(
                        document.uri.fsPath,
                        webviewPanel.webview,
                        jumpMsg.lineNumber,
                        jumpMsg.tokenizer
                    );
                    break;
                case 'openInTextEditor':
                    const doc = await vscode.workspace.openTextDocument(document.uri);
                    await vscode.window.showTextDocument(doc, { preview: false });
                    break;
            }
        });
    }

    /**
     * Load and send rows to webview with token counting
     */
    protected async loadAndSendRows(
        filePath: string,
        webview: vscode.Webview,
        offset: number,
        limit: number,
        searchTerm?: string,
        tokenizer: string = 'gpt-4'
    ): Promise<void> {
        const loader = this.createLoader(filePath);

        try {
            await loader.initialize(filePath);

            const filter = searchTerm ? { searchTerm } : undefined;
            const batch = await loader.loadRows(offset, limit, filter);

            // Count tokens for each row
            const tokenCounts: { [index: number]: number } = {};
            for (const row of batch.rows) {
                try {
                    const text = loader.extractTextForTokens(row.data);
                    const tokens = await countTokens(text, tokenizer);
                    tokenCounts[row.index] = tokens;
                    row.tokens = tokens;
                } catch (error) {
                    console.error(`Error counting tokens for row ${row.index}:`, error);
                }
            }

            // Send rows to webview
            webview.postMessage({
                type: 'lines',
                lines: batch.rows,
                hasMore: batch.hasMore,
                nextOffset: batch.nextOffset
            });

            // Send token counts
            webview.postMessage({
                type: 'tokens',
                counts: tokenCounts
            });
        } finally {
            loader.dispose();
        }
    }

    /**
     * Jump to a specific row and load from that point
     */
    protected async jumpToRow(
        filePath: string,
        webview: vscode.Webview,
        targetRow: number,
        tokenizer: string = 'gpt-4'
    ): Promise<void> {
        await this.loadAndSendRows(filePath, webview, targetRow, 100, undefined, tokenizer);
    }

    /**
     * Load HTML template and inject resource URIs
     */
    protected getHtmlForWebview(webview: vscode.Webview): string {
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
