import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { JsonlEditorProvider } from './jsonlEditorProvider';
import { JsonlTextViewProvider } from './jsonlTextViewProvider';

/**
 * Pattern B: single persistent webview panel (reused across opens).
 *
 * This intentionally co-exists with the existing Custom Editor implementation
 * so we can A/B benchmark webview initialization latency.
 */
export class JsonlSingletonPanel {
    private static current: JsonlSingletonPanel | undefined;

    private readonly panel: vscode.WebviewPanel;
    private readonly provider: JsonlEditorProvider;
    private currentFilePath: string | undefined;

    private constructor(private readonly context: vscode.ExtensionContext) {
        this.provider = new JsonlEditorProvider(context);

        this.panel = vscode.window.createWebviewPanel(
            'mlWorkbench.jsonlViewerFast',
            'JSONL Viewer (Fast)',
            vscode.ViewColumn.Active,
            {
                enableScripts: true,
                retainContextWhenHidden: true,
            }
        );

        // Reuse existing HTML/UI without forking it.
        // Note: JsonlEditorProvider.getHtmlForWebview is private; we use a narrow cast
        // to avoid duplicating the huge HTML blob for this benchmark-only path.
        this.panel.webview.html = (this.provider as any).getHtmlForWebview(this.panel.webview);

        this.panel.onDidDispose(() => {
            JsonlSingletonPanel.current = undefined;
        });

        this.panel.webview.onDidReceiveMessage(async (message) => {
            switch (message.type) {
                case 'webviewReady':
                    // Webview script just finished loading; (re)send current file so content loads
                    await this.syncContentToWebview();
                    break;
                case 'loadLines': {
                    if (!this.currentFilePath) return;
                    await (this.provider as any).loadLines(
                        this.currentFilePath,
                        this.panel.webview,
                        message.offset,
                        message.limit,
                        message.searchTerm,
                        message.tokenizer
                    );
                    break;
                }
                case 'jumpToLine': {
                    if (!this.currentFilePath) return;
                    await (this.provider as any).jumpToLine(
                        this.currentFilePath,
                        this.panel.webview,
                        message.lineNumber,
                        message.tokenizer
                    );
                    break;
                }
                case 'openInTextEditor': {
                    if (!this.currentFilePath) return;
                    const uri = vscode.Uri.file(this.currentFilePath);
                    const doc = await vscode.workspace.openTextDocument(uri);
                    await vscode.window.showTextDocument(doc, { preview: false });
                    break;
                }
            }
        });
    }

    static async open(context: vscode.ExtensionContext, uri?: vscode.Uri): Promise<void> {
        if (!JsonlSingletonPanel.current) {
            JsonlSingletonPanel.current = new JsonlSingletonPanel(context);
        }

        const rawUri = uri ?? vscode.window.activeTextEditor?.document?.uri;
        if (!rawUri) return;
        // Resolve jsonl-view (ASCII text viewer) URI to file URI so loading works
        const targetUri = JsonlTextViewProvider.getFileUri(rawUri) ?? rawUri;

        await JsonlSingletonPanel.current.loadFile(targetUri);
        JsonlSingletonPanel.current.panel.reveal(vscode.ViewColumn.Active);
    }

    private async loadFile(uri: vscode.Uri): Promise<void> {
        this.currentFilePath = uri.fsPath;
        await this.syncContentToWebview();
    }

    /** Send clear + fileInfo + initial lines to the webview. Called from loadFile and on webviewReady. */
    private async syncContentToWebview(): Promise<void> {
        if (!this.currentFilePath) return;
        const uri = vscode.Uri.file(this.currentFilePath);
        const startTime = Date.now();

        this.panel.webview.postMessage({ type: 'clear' });

        const stats = await fs.promises.stat(uri.fsPath);
        const fileSizeBytes = stats.size;
        const fileSizeMB = (fileSizeBytes / 1024 / 1024).toFixed(2);

        this.panel.webview.postMessage({
            type: 'fileInfo',
            filePath: uri.fsPath,
            fileName: path.basename(uri.fsPath),
            fileSize: fileSizeBytes,
            fileSizeMB: fileSizeMB,
            backendTimestamp: Date.now(),
            backendTimeSinceStart: Date.now() - startTime,
        });

        await (this.provider as any).loadLines(uri.fsPath, this.panel.webview, 0, 100);
    }
}

