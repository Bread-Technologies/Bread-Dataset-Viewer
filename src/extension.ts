import * as vscode from 'vscode';
import { JsonlDataProvider } from './providers/JsonlDataProvider';
import { JsonDataProvider } from './providers/JsonDataProvider';
import { ParquetDataProvider } from './providers/ParquetDataProvider';
import { CsvDataProvider } from './providers/CsvDataProvider';
import { ArrowDataProvider } from './providers/ArrowDataProvider';
import { cleanup as cleanupTokenizer, getTokenizerOptions } from './utils/tokenizer';
import { GenericTextViewProvider } from './textViewer/GenericTextViewProvider';
import { DecorationManager } from './textViewer/DecorationManager';
import { JsonDecorator } from './textViewer/decorators/JsonDecorator';
import { CsvDecorator } from './textViewer/decorators/CsvDecorator';
import { NoOpDecorator } from './textViewer/decorators/NoOpDecorator';
import { TEXT_VIEWER_HEADER_ACTIONS } from './textViewer/BaseTextViewProvider';
import { TelemetryService } from './telemetry/TelemetryService';
import { TELEMETRY_CONFIG, isTelemetryConfigured } from './config/telemetry.config';

export async function activate(context: vscode.ExtensionContext) {
    const activationStart = Date.now();

    // Initialize telemetry service (if configured)
    if (isTelemetryConfigured()) {
        TelemetryService.initialize(context, TELEMETRY_CONFIG.appInsightsKey);
    }

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

    // Multi-Format Text Viewer (Generic ASCII viewer for all formats)
    const genericTextProvider = new GenericTextViewProvider(context);
    context.subscriptions.push(
        vscode.workspace.registerTextDocumentContentProvider(
            GenericTextViewProvider.scheme,
            genericTextProvider
        )
    );

    // Setup decorations for each format
    const decorationManager = new DecorationManager(context);
    decorationManager.registerDecorator('jsonl', new JsonDecorator());
    decorationManager.registerDecorator('json', new JsonDecorator());
    decorationManager.registerDecorator('csv', new CsvDecorator());
    decorationManager.registerDecorator('tsv', new CsvDecorator());
    decorationManager.registerDecorator('parquet', new JsonDecorator()); // Parquet renders as cards
    decorationManager.registerDecorator('arrow', new JsonDecorator()); // Arrow renders as cards
    decorationManager.registerDecorator('feather', new JsonDecorator()); // Feather renders as cards

    // Apply decorations when active editor changes
    context.subscriptions.push(
        vscode.window.onDidChangeActiveTextEditor(editor => {
            if (editor?.document.uri.scheme === GenericTextViewProvider.scheme) {
                const state = genericTextProvider.getState(editor.document.uri);
                if (state) {
                    decorationManager.applyDecorations(editor, state.format);
                }
            }
        })
    );

    // Reapply decorations when document content changes
    context.subscriptions.push(
        vscode.workspace.onDidChangeTextDocument(event => {
            const editor = vscode.window.activeTextEditor;
            if (editor?.document === event.document &&
                event.document.uri.scheme === GenericTextViewProvider.scheme) {
                const state = genericTextProvider.getState(event.document.uri);
                if (state) {
                    decorationManager.applyDecorations(editor, state.format);
                }
            }
        })
    );

    // Generic "Open Text Viewer" command for all formats
    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.openTextViewer', async (uri?: vscode.Uri) => {
            const fileUri = uri ?? vscode.window.activeTextEditor?.document.uri;
            if (!fileUri || fileUri.scheme !== 'file') {
                vscode.window.showErrorMessage('No file selected');
                return;
            }

            // Detect format from extension
            const ext = fileUri.fsPath.split('.').pop()?.toLowerCase();
            const supportedFormats = ['jsonl', 'json', 'csv', 'tsv', 'parquet', 'arrow', 'feather'];

            if (!ext || !supportedFormats.includes(ext)) {
                vscode.window.showErrorMessage(`Unsupported format: ${ext}`);
                return;
            }

            // Create view URI
            const viewUri = GenericTextViewProvider.toViewUri(fileUri, ext);

            // Open in text viewer
            const doc = await vscode.workspace.openTextDocument(viewUri);
            const editor = await vscode.window.showTextDocument(doc, { preview: false });

            // Apply decorations
            const state = genericTextProvider.getState(viewUri);
            if (state) {
                decorationManager.applyDecorations(editor, state.format);
            }

            // Track text viewer opened
            if (isTelemetryConfigured()) {
                TelemetryService.getInstance().sendEvent('textviewer.opened', {
                    format: ext,
                    viewerType: 'text',
                });
            }
        })
    );

    // Document link provider for generic text viewer (makes header actions clickable)
    context.subscriptions.push(
        vscode.languages.registerDocumentLinkProvider(
            { scheme: GenericTextViewProvider.scheme },
            {
                provideDocumentLinks(document: vscode.TextDocument): vscode.DocumentLink[] {
                    const links: vscode.DocumentLink[] = [];
                    const linkLineIndex = 1;
                    if (document.lineCount <= linkLineIndex) return links;
                    const lineText = document.lineAt(linkLineIndex).text;
                    const tokens = [
                        { str: TEXT_VIEWER_HEADER_ACTIONS.NEXT, command: 'mlWorkbench.textViewer.nextPage' },
                        { str: TEXT_VIEWER_HEADER_ACTIONS.PREV, command: 'mlWorkbench.textViewer.prevPage' },
                        { str: TEXT_VIEWER_HEADER_ACTIONS.SEARCH, command: 'mlWorkbench.textViewer.search' },
                        { str: TEXT_VIEWER_HEADER_ACTIONS.GOTO, command: 'mlWorkbench.textViewer.gotoLine' },
                        { str: TEXT_VIEWER_HEADER_ACTIONS.CARDS, command: 'mlWorkbench.textViewer.setMode', args: ['cards'] },
                        { str: TEXT_VIEWER_HEADER_ACTIONS.EDIT, command: 'mlWorkbench.textViewer.openInEditor' },
                        { str: TEXT_VIEWER_HEADER_ACTIONS.TOKENIZER, command: 'mlWorkbench.textViewer.setTokenizer' },
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
        const scheme = editor.document.uri.scheme;
        if (scheme !== GenericTextViewProvider.scheme || editor.visibleRanges.length === 0) return null;
        const w = Math.max(...editor.visibleRanges.map(r => r.end.character));
        return w > 0 ? w : null;
    };

    // Resize header and cards when the editor pane is resized (htop/ncdu-style)
    context.subscriptions.push(
        vscode.window.onDidChangeTextEditorVisibleRanges((e: vscode.TextEditorVisibleRangesChangeEvent) => {
            const scheme = e.textEditor.document.uri.scheme;
            if (scheme === GenericTextViewProvider.scheme) {
                const width = sampleColumnWidth(e.textEditor);
                if (width != null) genericTextProvider.setColumnWidth(e.textEditor.document.uri, width, true);
            }
        })
    );

    // When a generic text viewer editor becomes active, sample width after a short delay
    context.subscriptions.push(
        vscode.window.onDidChangeActiveTextEditor(editor => {
            if (!editor || editor.document.uri.scheme !== GenericTextViewProvider.scheme) return;
            const viewUri = editor.document.uri;
            const run = () => {
                const ed = vscode.window.activeTextEditor;
                if (!ed || ed.document.uri.toString() !== viewUri.toString()) return;
                const width = sampleColumnWidth(ed);
                if (width != null) genericTextProvider.setColumnWidth(viewUri, width, true);
            };
            setTimeout(run, 50);
            setTimeout(run, 200);
        })
    );

    // Generic text viewer commands
    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.textViewer.setMode', async (mode?: 'cards') => {
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.uri.scheme !== GenericTextViewProvider.scheme) return;
            if (mode !== 'cards') return;

            const state = genericTextProvider.getState(editor.document.uri);
            genericTextProvider.updateState(editor.document.uri, st => {
                st.mode = mode;
            });

            // Track mode change
            if (isTelemetryConfigured() && state) {
                TelemetryService.getInstance().sendEvent('textviewer.mode.changed', {
                    format: state.format,
                    mode: mode,
                });
            }
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.textViewer.nextPage', async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.uri.scheme !== GenericTextViewProvider.scheme) return;

            const state = genericTextProvider.getState(editor.document.uri);
            genericTextProvider.updateState(editor.document.uri, st => {
                st.startLine = Math.max(0, st.startLine + st.pageSize);
            });

            // Track pagination
            if (isTelemetryConfigured() && state) {
                TelemetryService.getInstance().sendEvent('textviewer.pagination', {
                    format: state.format,
                    action: 'next',
                });
            }

            // Reapply decorations after content refresh
            setTimeout(() => {
                const state = genericTextProvider.getState(editor.document.uri);
                if (state) decorationManager.applyDecorations(editor, state.format);
            }, 50);
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.textViewer.prevPage', async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.uri.scheme !== GenericTextViewProvider.scheme) return;

            const state = genericTextProvider.getState(editor.document.uri);
            genericTextProvider.updateState(editor.document.uri, st => {
                st.startLine = Math.max(0, st.startLine - st.pageSize);
            });

            // Track pagination
            if (isTelemetryConfigured() && state) {
                TelemetryService.getInstance().sendEvent('textviewer.pagination', {
                    format: state.format,
                    action: 'prev',
                });
            }

            // Reapply decorations after content refresh
            setTimeout(() => {
                const state = genericTextProvider.getState(editor.document.uri);
                if (state) decorationManager.applyDecorations(editor, state.format);
            }, 50);
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.textViewer.search', async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.uri.scheme !== GenericTextViewProvider.scheme) return;
            const uri = editor.document.uri;
            const state = genericTextProvider.getState(uri);
            let current: string | null = null;
            genericTextProvider.updateState(uri, st => {
                current = st.search;
            });
            const pattern = await vscode.window.showInputBox({
                prompt: 'Search lines (substring match)',
                value: current ?? '',
            });

            const wasCleared = current && (!pattern || pattern.length === 0);
            const wasPerformed = pattern && pattern.length > 0;

            genericTextProvider.updateState(uri, st => {
                st.search = pattern && pattern.length > 0 ? pattern : null;
                st.startLine = 0;
            });

            // Track search (without actual search term for privacy)
            if (isTelemetryConfigured() && state) {
                if (wasCleared) {
                    TelemetryService.getInstance().sendEvent('textviewer.search.cleared', {
                        format: state.format,
                    });
                } else if (wasPerformed) {
                    // Categorize search term length without sending actual term
                    let lengthCategory = 'empty';
                    if (pattern!.length > 0 && pattern!.length <= 3) lengthCategory = 'short';
                    else if (pattern!.length <= 10) lengthCategory = 'medium';
                    else lengthCategory = 'long';

                    TelemetryService.getInstance().sendEvent('textviewer.search.performed', {
                        format: state.format,
                        searchLengthCategory: lengthCategory,
                    });
                }
            }
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.textViewer.gotoLine', async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.uri.scheme !== GenericTextViewProvider.scheme) return;
            const state = genericTextProvider.getState(editor.document.uri);
            const value = await vscode.window.showInputBox({
                prompt: 'Go to line',
            });
            if (!value) return;
            const n = Number.parseInt(value, 10);
            if (Number.isNaN(n) || n < 0) return;

            const startTime = Date.now();
            genericTextProvider.updateState(editor.document.uri, st => {
                st.startLine = n;
            });

            // Track jump to line
            if (isTelemetryConfigured() && state) {
                TelemetryService.getInstance().sendEvent('textviewer.jumpToLine', {
                    format: state.format,
                }, {
                    durationMs: Date.now() - startTime,
                });
            }
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.textViewer.openInEditor', async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.uri.scheme !== GenericTextViewProvider.scheme) return;
            const state = genericTextProvider.getState(editor.document.uri);
            const fileUri = GenericTextViewProvider.getFileUri(editor.document.uri);
            if (!fileUri) return;

            // Track opening in editor
            if (isTelemetryConfigured() && state) {
                TelemetryService.getInstance().sendEvent('textviewer.openInEditor', {
                    format: state.format,
                });
            }

            const doc = await vscode.workspace.openTextDocument(fileUri);
            await vscode.window.showTextDocument(doc, { preview: false });
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.textViewer.setTokenizer', async () => {
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.uri.scheme !== GenericTextViewProvider.scheme) return;
            const uri = editor.document.uri;
            const state = genericTextProvider.getState(uri);
            const current = genericTextProvider.getTokenizer(uri);
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

            const newTokenizer = picked.label === '(none)' ? null : (picked.description ?? null);
            genericTextProvider.updateState(uri, st => {
                st.tokenizer = newTokenizer;
            });

            // Track tokenizer selection
            if (isTelemetryConfigured() && state) {
                TelemetryService.getInstance().sendEvent('textviewer.tokenizer.selected', {
                    format: state.format,
                    tokenizerType: newTokenizer ?? 'none',
                    tokenizerName: picked.label,
                    previousTokenizer: current ?? 'none',
                });
            }
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

    // Send activation complete event
    if (isTelemetryConfigured()) {
        const telemetry = TelemetryService.getInstance();
        telemetry.sendEvent('extension.activated', {
            activationReason: String(context.extensionMode),
        }, {
            activationTimeMs: Date.now() - activationStart,
        });
    }
}

export function deactivate() {
    // Send deactivation event and dispose telemetry
    if (isTelemetryConfigured()) {
        const telemetry = TelemetryService.getInstance();
        telemetry.sendEvent('extension.deactivated');
        telemetry.dispose();
    }

    cleanupTokenizer();
    console.log('Bread Dataset Viewer extension is now deactivated');
}
