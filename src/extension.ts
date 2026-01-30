import * as vscode from 'vscode';
import { JsonlDataProvider } from './providers/JsonlDataProvider';
import { JsonDataProvider } from './providers/JsonDataProvider';
import { ParquetDataProvider } from './providers/ParquetDataProvider';
import { CsvDataProvider } from './providers/CsvDataProvider';
import { ArrowDataProvider } from './providers/ArrowDataProvider';
import { cleanup as cleanupTokenizer, getTokenizerOptions } from './utils/tokenizer';
import { JsonlEditorProvider } from './jsonlEditorProvider';
import { JsonlSingletonPanel } from './jsonlSingletonPanel';
import { JsonlTextViewProvider, JSONL_TEXT_HEADER_ACTIONS } from './jsonlTextViewProvider';
import { createJsonlDecorationTypes, applyJsonlDecorations } from './jsonlTextDecorations';

export async function activate(context: vscode.ExtensionContext) {
    console.log('ML Workbench extension is now active');

    // Register JSONL Viewer
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

    // Text-based JSONL Viewer (no webview, for latency benchmarking)
    const textProvider = new JsonlTextViewProvider(context);
    context.subscriptions.push(
        vscode.workspace.registerTextDocumentContentProvider(
            JsonlTextViewProvider.scheme,
            textProvider
        )
    );

    // Decoration types for text-view syntax coloring (dispose on deactivate)
    const jsonlDecorationTypes = createJsonlDecorationTypes();
    jsonlDecorationTypes.forEach(dt => context.subscriptions.push(dt));

    const updateJsonlViewDecorations = () => {
        const editor = vscode.window.activeTextEditor;
        if (editor?.document.uri.scheme !== JsonlTextViewProvider.scheme) return;
        applyJsonlDecorations(editor, jsonlDecorationTypes);
    };

    textProvider.onDidChange(uri => {
        const editor = vscode.window.activeTextEditor;
        if (editor?.document.uri.toString() === uri.toString()) {
            updateJsonlViewDecorations();
        }
    });

    context.subscriptions.push(
        vscode.window.onDidChangeActiveTextEditor(editor => {
            if (editor?.document.uri.scheme === JsonlTextViewProvider.scheme) {
                updateJsonlViewDecorations();
            }
        })
    );

    // Reapply decorations after document content updates (fixes color reversion bug during navigation)
    context.subscriptions.push(
        vscode.workspace.onDidChangeTextDocument(e => {
            // Only handle jsonl-view documents
            if (e.document.uri.scheme !== JsonlTextViewProvider.scheme) return;

            // Find the editor showing this document
            const editor = vscode.window.visibleTextEditors.find(ed => ed.document === e.document);
            if (!editor) return;

            // Reapply decorations with the updated content
            applyJsonlDecorations(editor, jsonlDecorationTypes);
        })
    );

    // Turn header action labels into clickable command links
    context.subscriptions.push(
        vscode.languages.registerDocumentLinkProvider(
            { scheme: JsonlTextViewProvider.scheme },
            {
                provideDocumentLinks(document: vscode.TextDocument): vscode.DocumentLink[] {
                    const links: vscode.DocumentLink[] = [];
                    // Header has a leading blank line, so the link line is at index 1
                    const linkLineIndex = 1;
                    if (document.lineCount <= linkLineIndex) return links;
                    const lineText = document.lineAt(linkLineIndex).text;
                    const tokens = [
                        { str: JSONL_TEXT_HEADER_ACTIONS.NEXT, command: 'mlWorkbench.jsonlText.nextPage' },
                        { str: JSONL_TEXT_HEADER_ACTIONS.PREV, command: 'mlWorkbench.jsonlText.prevPage' },
                        { str: JSONL_TEXT_HEADER_ACTIONS.SEARCH, command: 'mlWorkbench.jsonlText.search' },
                        { str: JSONL_TEXT_HEADER_ACTIONS.GOTO, command: 'mlWorkbench.jsonlText.gotoLine' },
                        { str: JSONL_TEXT_HEADER_ACTIONS.CARDS, command: 'mlWorkbench.jsonlText.setMode', args: ['cards'] },
                        { str: JSONL_TEXT_HEADER_ACTIONS.EDIT, command: 'mlWorkbench.jsonlText.openInEditor' },
                        { str: JSONL_TEXT_HEADER_ACTIONS.TOKENIZER, command: 'mlWorkbench.jsonlText.setTokenizer' },
                    ];
                    for (const { str, command, args } of tokens) {
                        let idx = 0;
                        while (true) {
                            const pos = lineText.indexOf(str, idx);
                            if (pos === -1) break;
                            const range = new vscode.Range(linkLineIndex, pos, linkLineIndex, pos + str.length);
                            const query = args ? '?' + encodeURIComponent(JSON.stringify(args)) : '';
                            const target = vscode.Uri.parse(`command:${command}${query}`);
                            links.push(new vscode.DocumentLink(range, target));
                            idx = pos + 1;
                        }
                    }
                    return links;
                },
            }
        )
    );

    // Sample viewport width from visible ranges (only reliable when every line is long enough).
    const sampleColumnWidth = (editor: vscode.TextEditor): number | null => {
        if (editor.document.uri.scheme !== JsonlTextViewProvider.scheme || editor.visibleRanges.length === 0) return null;
        const w = Math.max(...editor.visibleRanges.map(r => r.end.character));
        return w > 0 ? w : null;
    };

    // Resize header and cards when the editor pane is resized (htop/ncdu-style)
    context.subscriptions.push(
        vscode.window.onDidChangeTextEditorVisibleRanges((e: vscode.TextEditorVisibleRangesChangeEvent) => {
            if (e.textEditor.document.uri.scheme !== JsonlTextViewProvider.scheme) return;
            const width = sampleColumnWidth(e.textEditor);
            // Use growOnly to prevent shrinking during navigation transitions
            if (width != null) textProvider.setColumnWidth(e.textEditor.document.uri, width, true);
        })
    );

    // When a jsonl-view editor becomes active, sample width after a short delay (layout may not be ready immediately).
    context.subscriptions.push(
        vscode.window.onDidChangeActiveTextEditor(editor => {
            if (!editor || editor.document.uri.scheme !== JsonlTextViewProvider.scheme) return;
            const viewUri = editor.document.uri;
            const run = () => {
                const ed = vscode.window.activeTextEditor;
                if (!ed || ed.document.uri.toString() !== viewUri.toString()) return;
                const width = sampleColumnWidth(ed);
                // Use growOnly to prevent shrinking during navigation
                if (width != null) textProvider.setColumnWidth(viewUri, width, true);
            };
            setTimeout(run, 50);
            setTimeout(run, 200);
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.openJsonlTextViewer', async (uri?: vscode.Uri) => {
            const raw = uri ?? vscode.window.activeTextEditor?.document.uri;
            if (!raw) {
                return;
            }
            const target = JsonlTextViewProvider.getFileUri(raw) ?? raw;
            const viewUri = JsonlTextViewProvider.toViewUri(target);
            const doc = await vscode.workspace.openTextDocument(viewUri);
            await vscode.window.showTextDocument(doc, { preview: false });
            // Use plaintext so no grammar tokenizes box-drawing chars (┌│─ etc.) and causes pink/weird colors
            await vscode.languages.setTextDocumentLanguage(doc, 'plaintext');
            // Poll for viewport width until layout is ready (provider pads all lines so visibleRanges reflects real width).
            const trySetWidth = () => {
                const editor = vscode.window.activeTextEditor;
                if (editor?.document.uri.toString() !== viewUri.toString()) return;
                const width = sampleColumnWidth(editor);
                // Use growOnly to prevent shrinking during navigation
                if (width != null && width >= 40) textProvider.setColumnWidth(viewUri, width, true);
            };
            [50, 150, 400, 1000].forEach(ms => setTimeout(trySetWidth, ms));
            [100, 300].forEach(ms => setTimeout(updateJsonlViewDecorations, ms));
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.jsonlText.setMode', async (mode?: 'cards') => {
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.uri.scheme !== JsonlTextViewProvider.scheme) {
                return;
            }
            if (mode !== 'cards') {
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
            // Add timeout to ensure decorations reapply after content refresh
            setTimeout(() => updateJsonlViewDecorations(), 50);
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
            // Add timeout to ensure decorations reapply after content refresh
            setTimeout(() => updateJsonlViewDecorations(), 50);
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.jsonlText.search', async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.uri.scheme !== JsonlTextViewProvider.scheme) {
                return;
            }
            const uri = editor.document.uri;
            let current: string | null = null;
            textProvider.updateState(uri, st => {
                current = st.search;
            });
            const pattern = await vscode.window.showInputBox({
                prompt: 'Search lines (substring match)',
                value: current ?? '',
            });
            textProvider.updateState(uri, st => {
                st.search = pattern && pattern.length > 0 ? pattern : null;
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

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.jsonlText.openInEditor', async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.uri.scheme !== JsonlTextViewProvider.scheme) return;
            const fileUri = JsonlTextViewProvider.getFileUri(editor.document.uri);
            if (!fileUri) return;
            const doc = await vscode.workspace.openTextDocument(fileUri);
            await vscode.window.showTextDocument(doc, { preview: false });
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.jsonlText.setTokenizer', async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.uri.scheme !== JsonlTextViewProvider.scheme) return;
            const uri = editor.document.uri;
            const current = textProvider.getTokenizer(uri);
            const options = getTokenizerOptions();
            const items: vscode.QuickPickItem[] = [
                { label: '(none)', description: 'No tokenizer' },
                ...options.map(opt => ({
                    label: opt.label,
                    description: opt.id,
                })),
            ];
            const picked = await vscode.window.showQuickPick(items, {
                title: 'Tokenizer',
                placeHolder: current ? options.find(o => o.id === current)?.label ?? current : '(none)',
                matchOnDescription: true,
            });
            if (picked === undefined) return;
            textProvider.updateState(uri, st => {
                st.tokenizer = picked.label === '(none)' ? null : (picked.description ?? null);
            });
        })
    );

    // Fast JSONL Viewer (single persistent panel)
    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.openJsonlFast', async (uri?: vscode.Uri) => {
            const raw = uri ?? vscode.window.activeTextEditor?.document.uri;
            const target = raw ? (JsonlTextViewProvider.getFileUri(raw) ?? raw) : undefined;
            await JsonlSingletonPanel.open(context, target);
        })
    );

    // Register JSON Viewer
    const jsonProvider = new JsonDataProvider(context);
    context.subscriptions.push(
        vscode.window.registerCustomEditorProvider(
            'mlWorkbench.jsonViewer',
            jsonProvider,
            {
                webviewOptions: {
                    retainContextWhenHidden: true,
                },
                supportsMultipleEditorsPerDocument: false,
            }
        )
    );

    // Register Parquet Viewer
    const parquetProvider = new ParquetDataProvider(context);
    context.subscriptions.push(
        vscode.window.registerCustomEditorProvider(
            'mlWorkbench.parquetViewer',
            parquetProvider,
            {
                webviewOptions: {
                    retainContextWhenHidden: true,
                },
                supportsMultipleEditorsPerDocument: false,
            }
        )
    );

    // Register CSV/TSV Viewer
    const csvProvider = new CsvDataProvider(context);
    context.subscriptions.push(
        vscode.window.registerCustomEditorProvider(
            'mlWorkbench.csvViewer',
            csvProvider,
            {
                webviewOptions: {
                    retainContextWhenHidden: true,
                },
                supportsMultipleEditorsPerDocument: false,
            }
        )
    );

    // Register Arrow IPC Viewer
    const arrowProvider = new ArrowDataProvider(context);
    context.subscriptions.push(
        vscode.window.registerCustomEditorProvider(
            'mlWorkbench.arrowViewer',
            arrowProvider,
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
