import * as vscode from 'vscode';
// Old provider kept as backup during migration
// import { JsonlEditorProvider } from './jsonlEditorProvider';
import { JsonlDataProvider } from './providers/JsonlDataProvider';
import { ModelChatProvider } from './modelChatProvider';
import { initializeBackends } from './backends';
import { initTokenizer, cleanup as cleanupTokenizer } from './utils/tokenizer';

export async function activate(context: vscode.ExtensionContext) {
    console.log('ML Workbench extension is now active');

    // Initialize tokenizer for accurate token counting
    await initTokenizer();

    // Initialize backends (Ollama, etc.)
    await initializeBackends(context);

    // Register JSONL Viewer (new architecture)
    const jsonlProvider = new JsonlDataProvider(context);
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
