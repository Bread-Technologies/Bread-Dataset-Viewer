import * as vscode from 'vscode';
import * as fs from 'fs';
import { IDataLoader, DataRow } from '../formats/interfaces';
import { getTokenizerName, countTokens } from '../utils/tokenizer';
import { ITextRenderer, TextViewerState } from './renderers/ITextRenderer';

const DEFAULT_COLUMN_WIDTH = 120;
const MIN_COLUMN_WIDTH = 40;
const MAX_COLUMN_WIDTH = 500;

/** Action labels in the header; DocumentLinkProvider turns these into command links. */
export const TEXT_VIEWER_HEADER_ACTIONS = {
    NEXT: '[Next]',
    PREV: '[Prev]',
    SEARCH: '[Search]',
    GOTO: '[Goto]',
    CARDS: '[Cards]',
    EDIT: '[Edit]',
    TOKENIZER: '[Tokenizer]',
} as const;

/**
 * Abstract base provider for text-based multi-format viewers
 * Provides common pagination, search, and token counting logic
 */
export abstract class BaseTextViewProvider implements vscode.TextDocumentContentProvider {
    protected readonly emitter = new vscode.EventEmitter<vscode.Uri>();
    protected readonly state = new Map<string, TextViewerState>();

    readonly onDidChange = this.emitter.event;

    constructor(
        protected readonly context: vscode.ExtensionContext,
        public readonly scheme: string
    ) {}

    /**
     * Create format-specific data loader
     * @param fileUri - The file URI to load data from
     */
    abstract createLoader(fileUri: vscode.Uri): IDataLoader;

    /**
     * Create format-specific renderer
     * @param format - The file format (jsonl, csv, etc.)
     */
    abstract createRenderer(format: string): ITextRenderer;

    /** Resolve a view URI to the underlying file URI */
    protected fromViewUri(viewUri: vscode.Uri): vscode.Uri {
        const encoded = viewUri.path.replace(/^\//, '');
        const decoded = decodeURIComponent(encoded);
        const parsedUri = vscode.Uri.parse(decoded);
        return parsedUri.scheme === 'file' ? parsedUri : viewUri;
    }

    /** Get or initialize state for a view URI */
    protected getOrInitState(viewUri: vscode.Uri): TextViewerState {
        const key = viewUri.toString();
        let st = this.state.get(key);
        if (!st) {
            const fileUri = this.fromViewUri(viewUri);
            const format = this.detectFormat(fileUri);
            st = {
                fileUri,
                format,
                startLine: 0,
                pageSize: 100,
                search: null,
                tokenizer: null,
                columnWidth: DEFAULT_COLUMN_WIDTH,
                mode: 'cards',
            };
            this.state.set(key, st);
        }
        return st;
    }

    /** Detect format from file extension */
    protected detectFormat(fileUri: vscode.Uri): string {
        const ext = fileUri.fsPath.split('.').pop()?.toLowerCase();
        return ext || 'jsonl';
    }

    /** Public accessor for getting state (used by decoration manager) */
    public getState(viewUri: vscode.Uri): TextViewerState | undefined {
        return this.state.get(viewUri.toString());
    }

    /** Update state and trigger refresh */
    public updateState(viewUri: vscode.Uri, updater: (st: TextViewerState) => void): void {
        const st = this.getOrInitState(viewUri);
        updater(st);
        this.emitter.fire(viewUri);
    }

    /** Get current column width */
    public getColumnWidth(viewUri: vscode.Uri): number {
        return this.getOrInitState(viewUri).columnWidth;
    }

    /** Get current view mode */
    public getViewMode(viewUri: vscode.Uri): 'cards' | 'table' | 'raw' {
        return this.getOrInitState(viewUri).mode;
    }

    /** Get current tokenizer */
    public getTokenizer(viewUri: vscode.Uri): string | null {
        return this.getOrInitState(viewUri).tokenizer;
    }

    /** Update column width and refresh */
    public setColumnWidth(viewUri: vscode.Uri, width: number, growOnly: boolean = false): void {
        const clamped = Math.max(MIN_COLUMN_WIDTH, Math.min(MAX_COLUMN_WIDTH, Math.floor(width)));
        const st = this.getOrInitState(viewUri);
        if (growOnly && clamped <= st.columnWidth) return;
        if (st.columnWidth === clamped) return;
        st.columnWidth = clamped;
        this.emitter.fire(viewUri);
    }

    /** Main entry point for providing document content */
    async provideTextDocumentContent(uri: vscode.Uri): Promise<string> {
        const state = this.getOrInitState(uri);
        const header = await this.buildHeader(state);
        const body = await this.render(state);
        return `${header}\n\n${body}`;
    }

    /** Build header with navigation and status */
    protected async buildHeader(state: TextViewerState): Promise<string> {
        const fileName = state.fileUri.fsPath.split(/[/\\]/).pop() ?? `file.${state.format}`;
        let fileSizeLabel = '';
        try {
            const stat = await fs.promises.stat(state.fileUri.fsPath);
            const mb = stat.size / (1024 * 1024);
            fileSizeLabel = mb >= 1 ? ` (${mb.toFixed(2)} MB)` : ` (${(stat.size / 1024).toFixed(1)} KB)`;
        } catch {
            fileSizeLabel = '';
        }
        const searchLabel = state.search ? `Search: "${state.search}"` : 'Search: (none)';
        const tokenizerLabel = state.tokenizer
            ? `Tokenizer: ${getTokenizerName(state.tokenizer) ?? state.tokenizer}`
            : 'Tokenizer: (none)';
        const rangeLabel = `Lines ${state.startLine}–${state.startLine + state.pageSize - 1}`;
        const pad = '   ';
        const sep = '    │    ';
        const line0 = [
            '  🍞  ',
            fileName,
            fileSizeLabel,
            sep,
            TEXT_VIEWER_HEADER_ACTIONS.PREV,
            pad,
            TEXT_VIEWER_HEADER_ACTIONS.NEXT,
            pad,
            TEXT_VIEWER_HEADER_ACTIONS.SEARCH,
            pad,
            TEXT_VIEWER_HEADER_ACTIONS.GOTO,
            sep,
            TEXT_VIEWER_HEADER_ACTIONS.CARDS,
            pad,
            TEXT_VIEWER_HEADER_ACTIONS.EDIT,
            pad,
            TEXT_VIEWER_HEADER_ACTIONS.TOKENIZER,
            sep,
            rangeLabel,
            sep,
            searchLabel,
            sep,
            tokenizerLabel,
        ].join('');
        const renderWidth = state.columnWidth;
        const line0Padded = line0.padEnd(Math.max(line0.length, renderWidth), ' ');
        const rule = '═'.repeat(renderWidth);
        return ['', line0Padded, rule].join('\n');
    }

    /** Render the current page of data */
    protected async render(state: TextViewerState): Promise<string> {
        const rows = await this.loadData(state);
        if (rows.length === 0) {
            return '(no records to display)';
        }

        // Token counting (async)
        let tokenCounts: (number | null)[] | undefined;
        if (state.tokenizer) {
            tokenCounts = await Promise.all(
                rows.map((r) =>
                    countTokens(r.raw ?? JSON.stringify(r.data), state.tokenizer!, 'auto')
                        .then((res) => res.count)
                        .catch(() => null)
                )
            );
        }

        // Delegate to format-specific renderer
        const renderer = this.createRenderer(state.format);
        return renderer.renderRows(rows, state, tokenCounts);
    }

    /** Load data using IDataLoader interface */
    protected async loadData(state: TextViewerState): Promise<DataRow[]> {
        const loader = this.createLoader(state.fileUri);
        try {
            await loader.initialize(state.fileUri.fsPath);

            const batch = await loader.loadRows(
                state.startLine,
                state.pageSize,
                { searchTerm: state.search ?? undefined }
            );

            return batch.rows;
        } finally {
            await loader.dispose();
        }
    }
}
