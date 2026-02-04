import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { IDataLoader, FileFormat } from '../formats/interfaces';
import { countTokens } from '../utils/tokenizer';
import { LoadLinesMessage, JumpToLineMessage } from '../webview/types/messages';
import { TelemetryService } from '../telemetry/TelemetryService';
import { getFileSizeCategory } from '../telemetry/helpers';
import { isTelemetryConfigured } from '../config/telemetry.config';

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
        const timerId = `resolveEditor:${document.uri.fsPath}`;

        try {
            // Start telemetry timer
            if (isTelemetryConfigured()) {
                TelemetryService.getInstance().startTimer(timerId);
            }

            // Setup webview options
            webviewPanel.webview.options = {
                enableScripts: true,
                localResourceRoots: [
                    vscode.Uri.file(this.context.extensionPath),
                ],
            };

            // Load HTML for webview
            webviewPanel.webview.html = this.getHtmlForWebview(webviewPanel.webview);

            // Get file stats
            const stats = await fs.promises.stat(document.uri.fsPath);
            const fileSizeBytes = stats.size;
            const fileSizeMB = (fileSizeBytes / 1024 / 1024).toFixed(2);

            // Initialize loader to get metadata
            const loader = this.createLoader(document.uri.fsPath);
            await loader.initialize(document.uri.fsPath);
            const metadata = await loader.getMetadata();

            // Track initialization performance
            if (isTelemetryConfigured()) {
                const telemetry = TelemetryService.getInstance();
                telemetry.sendEvent('perf.initialization', {
                    format: metadata.format,
                    loaderType: loader.constructor.name,
                }, {
                    durationMs: Date.now() - startTime,
                });
            }

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

            // Setup message handlers
            this.setupMessageHandlers(document, webviewPanel);

            // Load initial batch
            const loadStart = Date.now();
            await this.loadAndSendRows(document.uri.fsPath, webviewPanel.webview, 0, 100);

            // Track file opened with complete info
            if (isTelemetryConfigured()) {
                const telemetry = TelemetryService.getInstance();
                telemetry.sendEvent('file.opened', {
                    format: metadata.format,
                    sizeCategory: getFileSizeCategory(fileSizeBytes),
                    viewerType: 'webview',
                    hasSchema: metadata.schema ? 'true' : 'false',
                }, {
                    fileSizeBytes,
                    rowCount: metadata.totalRows || 0,
                });

                // Track initial load performance
                telemetry.sendEvent('file.loaded.initial', {
                    format: metadata.format,
                    sizeCategory: getFileSizeCategory(fileSizeBytes),
                    viewerType: 'webview',
                }, {
                    durationMs: Date.now() - loadStart,
                    rowsLoaded: 100,
                });

                // End overall editor resolution timer
                telemetry.endTimer(timerId, 'perf.editor.resolved', {
                    format: metadata.format,
                });
            }
        } catch (error) {
            // Track file loading errors
            if (isTelemetryConfigured()) {
                TelemetryService.getInstance().sendError('error.fileLoad', error as Error, {
                    errorType: 'initialization_failed',
                });
            }
            throw error;
        }
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

                    // Track pagination from webview
                    if (isTelemetryConfigured()) {
                        const loader = this.createLoader(document.uri.fsPath);
                        await loader.initialize(document.uri.fsPath);
                        const metadata = await loader.getMetadata();
                        loader.dispose();

                        TelemetryService.getInstance().sendEvent('webview.loadMore', {
                            format: metadata.format,
                            hasSearch: loadMsg.searchTerm ? 'true' : 'false',
                        }, {
                            offset: loadMsg.offset,
                            limit: loadMsg.limit,
                        });
                    }

                    await this.loadAndSendRows(
                        document.uri.fsPath,
                        webviewPanel.webview,
                        loadMsg.offset,
                        loadMsg.limit,
                        loadMsg.searchTerm,
                        loadMsg.tokenizer,
                        loadMsg.tokenMode
                    );
                    break;
                case 'jumpToLine':
                    const jumpMsg = message as JumpToLineMessage;

                    // Track jump to line from webview
                    if (isTelemetryConfigured()) {
                        const loader = this.createLoader(document.uri.fsPath);
                        await loader.initialize(document.uri.fsPath);
                        const metadata = await loader.getMetadata();
                        loader.dispose();

                        TelemetryService.getInstance().sendEvent('webview.jumpToLine', {
                            format: metadata.format,
                        }, {
                            lineNumber: jumpMsg.lineNumber,
                        });
                    }

                    await this.jumpToRow(
                        document.uri.fsPath,
                        webviewPanel.webview,
                        jumpMsg.lineNumber,
                        jumpMsg.tokenizer,
                        jumpMsg.tokenMode
                    );
                    break;
                case 'openInTextEditor':
                    // Track opening in text editor from webview
                    if (isTelemetryConfigured()) {
                        const loader = this.createLoader(document.uri.fsPath);
                        await loader.initialize(document.uri.fsPath);
                        const metadata = await loader.getMetadata();
                        loader.dispose();

                        TelemetryService.getInstance().sendEvent('webview.openInTextEditor', {
                            format: metadata.format,
                        });
                    }

                    // Use workbench command to reopen the current file in text editor
                    // This bypasses the 50MB extension synchronization limit
                    await vscode.commands.executeCommand('workbench.action.reopenTextEditor');
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
        tokenizer: string = 'qwen-3',
        tokenMode: string = 'auto'
    ): Promise<void> {
        const loadStart = Date.now();
        const loader = this.createLoader(filePath);

        try {
            await loader.initialize(filePath);
            const metadata = await loader.getMetadata();

            const filter = searchTerm ? { searchTerm } : undefined;
            const batch = await loader.loadRows(offset, limit, filter);

            // Track data load performance
            if (isTelemetryConfigured()) {
                const telemetry = TelemetryService.getInstance();
                telemetry.sendEvent('perf.dataLoad', {
                    format: metadata.format,
                    loaderType: loader.constructor.name,
                    hasFilter: searchTerm ? 'true' : 'false',
                }, {
                    durationMs: Date.now() - loadStart,
                    rowCount: batch.rows.length,
                });
            }

            // Send rows to webview immediately (without tokens)
            webview.postMessage({
                type: 'lines',
                lines: batch.rows,
                hasMore: batch.hasMore,
                nextOffset: batch.nextOffset
            });

            // Count tokens in background and send separately
            setImmediate(async () => {
                const tokenCountStart = Date.now();
                const tokensMap: { [index: number]: any } = {};
                const errors: string[] = [];

                // Track token counting start
                if (isTelemetryConfigured()) {
                    TelemetryService.getInstance().sendEvent('tokenizer.count.started', {
                        tokenizerType: tokenizer,
                        tokenMode: tokenMode,
                        format: metadata.format,
                    }, {
                        rowCount: batch.rows.length,
                    });
                }

                let successCount = 0;
                let errorCount = 0;

                for (const row of batch.rows) {
                    try {
                        const text = loader.extractTextForTokens(row.data);
                        const result = await countTokens(text, tokenizer, tokenMode);
                        tokensMap[row.index] = {
                            count: result.count,
                            mode: result.mode,
                            key: result.key,
                            preview: result.preview,
                        };
                        successCount++;
                    } catch (error) {
                        const errorMsg = String(error);
                        console.error(`Error counting tokens for row ${row.index}:`, error);
                        tokensMap[row.index] = {
                            count: 0,
                            mode: 'error',
                            error: errorMsg,
                        };
                        if (!errors.some(e => e === errorMsg)) {
                            errors.push(errorMsg);
                        }
                        errorCount++;
                    }
                }

                // Track token counting completion
                if (isTelemetryConfigured()) {
                    TelemetryService.getInstance().sendEvent('tokenizer.count.completed', {
                        tokenizerType: tokenizer,
                        tokenMode: tokenMode,
                        format: metadata.format,
                        hadErrors: errorCount > 0 ? 'true' : 'false',
                    }, {
                        rowCount: batch.rows.length,
                        successCount,
                        errorCount,
                        durationMs: Date.now() - tokenCountStart,
                    });
                }

                // Send token counts
                webview.postMessage({
                    type: 'tokens',
                    tokens: tokensMap
                });

                // Send errors if any
                if (errors.length > 0) {
                    webview.postMessage({
                        type: 'tokenErrors',
                        errors: errors
                    });
                }
            });
        } catch (error) {
            // Track data loading errors
            if (isTelemetryConfigured()) {
                TelemetryService.getInstance().sendError('error.dataLoad', error as Error, {
                    errorType: 'load_failed',
                    hasFilter: searchTerm ? 'true' : 'false',
                });
            }
            throw error;
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
        tokenizer: string = 'qwen-3',
        tokenMode: string = 'auto'
    ): Promise<void> {
        await this.loadAndSendRows(filePath, webview, targetRow, 100, undefined, tokenizer, tokenMode);
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
