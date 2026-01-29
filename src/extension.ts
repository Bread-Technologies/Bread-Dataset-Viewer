import * as vscode from 'vscode';
import { JsonlEditorProvider } from './jsonlEditorProvider';
import { ModelChatProvider } from './modelChatProvider';
import { initializeBackends } from './backends';
import { initTokenizer, cleanup as cleanupTokenizer } from './utils/tokenizer';
import { JsonlSingletonPanel } from './jsonlSingletonPanel';
import { JsonlTextViewProvider } from './jsonlTextViewProvider';

export async function activate(context: vscode.ExtensionContext) {
    console.log('ML Workbench extension is now active');

    // Initialize tokenizer for accurate token counting
    await initTokenizer();

    // Initialize backends (Ollama, etc.)
    await initializeBackends(context);

    // Register JSONL Viewer
    const jsonlProvider = new JsonlEditorProvider(context);
    context.subscriptions.push(
        vscode.window.registerCustomEditorProvider(
            'mlWorkbench.jsonlViewer',
            jsonlProvider,
            {
                webviewOptions: {
                    retainContextWhenHidden: true,
                },
                supportsMultipleEditorsPerDocument: false,
            }
        )
    );

    // Text-based JSONL Viewer (no webview, for latency benchmarking)
    const textProvider = new JsonlTextViewProvider(context);
    context.subscriptions.push(
        vscode.workspace.registerTextDocumentContentProvider(
            JsonlTextViewProvider.scheme,
            textProvider
        )
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.openJsonlTextViewer', async (uri?: vscode.Uri) => {
            const target = uri ?? vscode.window.activeTextEditor?.document.uri;
            if (!target) {
                return;
            }
            const viewUri = JsonlTextViewProvider.toViewUri(target);
            const doc = await vscode.workspace.openTextDocument(viewUri);
            await vscode.window.showTextDocument(doc, { preview: false });
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.jsonlText.setMode', async (mode: 'cards' | 'table' | 'raw') => {
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.uri.scheme !== JsonlTextViewProvider.scheme) {
                return;
            }
            textProvider.updateState(editor.document.uri, st => {
                st.viewMode = mode;
            });
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.jsonlText.nextPage', async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.uri.scheme !== JsonlTextViewProvider.scheme) {
                return;
            }
            textProvider.updateState(editor.document.uri, st => {
                st.startLine = Math.max(0, st.startLine + st.pageSize);
            });
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.jsonlText.prevPage', async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.uri.scheme !== JsonlTextViewProvider.scheme) {
                return;
            }
            textProvider.updateState(editor.document.uri, st => {
                st.startLine = Math.max(0, st.startLine - st.pageSize);
            });
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.jsonlText.filter', async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.uri.scheme !== JsonlTextViewProvider.scheme) {
                return;
            }
            const uri = editor.document.uri;
            let current: string | null = null;
            textProvider.updateState(uri, st => {
                current = st.filter;
            });
            const pattern = await vscode.window.showInputBox({
                prompt: 'Filter lines (substring match)',
                value: current ?? '',
            });
            textProvider.updateState(uri, st => {
                st.filter = pattern && pattern.length > 0 ? pattern : null;
                st.startLine = 0;
            });
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.jsonlText.gotoLine', async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.uri.scheme !== JsonlTextViewProvider.scheme) {
                return;
            }
            const value = await vscode.window.showInputBox({
                prompt: 'Go to line',
            });
            if (!value) {
                return;
            }
            const n = Number.parseInt(value, 10);
            if (Number.isNaN(n) || n < 0) {
                return;
            }
            textProvider.updateState(editor.document.uri, st => {
                st.startLine = n;
            });
        })
    );

    // Fast JSONL Viewer (single persistent panel)
    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.openJsonlFast', async (uri?: vscode.Uri) => {
            await JsonlSingletonPanel.open(context, uri);
        })
    );

    // Register Model Chat
    const modelChatProvider = new ModelChatProvider(context);
    context.subscriptions.push(
        vscode.window.registerCustomEditorProvider(
            'mlWorkbench.modelChat',
            modelChatProvider,
            {
                webviewOptions: {
                    retainContextWhenHidden: true,
                },
                supportsMultipleEditorsPerDocument: false,
            }
        )
    );

    console.log('ML Workbench: Custom editors registered');
}

export function deactivate() {
    cleanupTokenizer();
    console.log('ML Workbench extension is now deactivated');
}
