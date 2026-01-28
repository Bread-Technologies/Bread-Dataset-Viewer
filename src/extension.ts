import * as vscode from 'vscode';
import { JsonlEditorProvider } from './jsonlEditorProvider';
import { ModelChatProvider } from './modelChatProvider';
import { initializeBackends } from './backends';
import { initTokenizer, cleanup as cleanupTokenizer } from './utils/tokenizer';
import { JsonlSingletonPanel } from './jsonlSingletonPanel';

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
