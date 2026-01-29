import * as vscode from 'vscode';
import { JsonlEditorProvider } from './jsonlEditorProvider';
import { cleanup as cleanupTokenizer } from './utils/tokenizer';

export async function activate(context: vscode.ExtensionContext) {
    console.log('ML Workbench extension is now active');

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

    console.log('ML Workbench: JSONL Viewer registered');
}

export function deactivate() {
    cleanupTokenizer();
    console.log('ML Workbench extension is now deactivated');
}
