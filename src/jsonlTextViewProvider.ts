import * as vscode from 'vscode';
import * as fs from 'fs';
import * as readline from 'readline';
import { getTokenizerName, countTokens } from './utils/tokenizer';

export type ViewMode = 'cards';

const DEFAULT_COLUMN_WIDTH = 120;
const MIN_COLUMN_WIDTH = 40;
const MAX_COLUMN_WIDTH = 500;
/** Horizontal padding (spaces) between card border and content. */
const CARD_PAD_H = 2;
/** Vertical padding: blank lines between card border and content. */
const CARD_PAD_V = 1;

interface ViewerState {
    fileUri: vscode.Uri;
    viewMode: ViewMode;
    startLine: number;
    pageSize: number;
    search: string | null;
    /** Tokenizer key (e.g. 'qwen-3') or null for none. */
    tokenizer: string | null;
    /** Visible editor width (chars); set from onDidChangeTextEditorVisibleRanges. */
    columnWidth: number;
}

/** Action labels in the header; DocumentLinkProvider turns these into command links. */
export const JSONL_TEXT_HEADER_ACTIONS = {
    NEXT: '[Next]',
    PREV: '[Prev]',
    SEARCH: '[Search]',
    GOTO: '[Goto]',
    CARDS: '[Cards]',
    /** Open file in text editor (view raw / edit). */
    EDIT: '[Edit]',
    TOKENIZER: '[Tokenizer]',
} as const;

export class JsonlTextViewProvider implements vscode.TextDocumentContentProvider {
    public static readonly scheme = 'jsonl-view';

    private readonly emitter = new vscode.EventEmitter<vscode.Uri>();
    private readonly state = new Map<string, ViewerState>();

    readonly onDidChange = this.emitter.event;

    constructor(private readonly context: vscode.ExtensionContext) {}

    static toViewUri(fileUri: vscode.Uri): vscode.Uri {
        const encoded = encodeURIComponent(fileUri.toString());
        return vscode.Uri.parse(`${JsonlTextViewProvider.scheme}:/${encoded}`);
    }

    /** Resolve a view URI (or file URI) to the underlying file URI. Use when running open commands from the text viewer. */
    static getFileUri(uri: vscode.Uri): vscode.Uri | undefined {
        if (uri.scheme === JsonlTextViewProvider.scheme) {
            const encoded = uri.path.replace(/^\//, '');
            const decoded = decodeURIComponent(encoded);
            return vscode.Uri.parse(decoded);
        }
        if (uri.scheme === 'file') {
            return uri;
        }
        return undefined;
    }

    private fromViewUri(viewUri: vscode.Uri): vscode.Uri {
        const fileUri = JsonlTextViewProvider.getFileUri(viewUri);
        return fileUri ?? viewUri;
    }

    private getOrInitState(viewUri: vscode.Uri): ViewerState {
        const key = viewUri.toString();
        let st = this.state.get(key);
        if (!st) {
            const fileUri = this.fromViewUri(viewUri);
            st = {
                fileUri,
                viewMode: 'cards',
                startLine: 0,
                pageSize: 100,
                search: null,
                tokenizer: null,
                columnWidth: DEFAULT_COLUMN_WIDTH,
            };
            this.state.set(key, st);
        }
        return st;
    }

    public updateState(viewUri: vscode.Uri, updater: (st: ViewerState) => void): void {
        const st = this.getOrInitState(viewUri);
        updater(st);
        this.emitter.fire(viewUri);
    }

    /** Current column width for a view (for callers that only want to grow). */
    public getColumnWidth(viewUri: vscode.Uri): number {
        return this.getOrInitState(viewUri).columnWidth;
    }

    /** Current view mode (e.g. to skip decorations in raw view). */
    public getViewMode(viewUri: vscode.Uri): ViewMode {
        return this.getOrInitState(viewUri).viewMode;
    }

    /** Current tokenizer key or null. */
    public getTokenizer(viewUri: vscode.Uri): string | null {
        return this.getOrInitState(viewUri).tokenizer;
    }

    /** Update visible column width and refresh (call when editor is resized). */
    public setColumnWidth(viewUri: vscode.Uri, width: number, growOnly: boolean = false): void {
        const clamped = Math.max(MIN_COLUMN_WIDTH, Math.min(MAX_COLUMN_WIDTH, Math.floor(width)));
        const st = this.getOrInitState(viewUri);
        // If growOnly is true, only update if new width is larger (prevents shrinking during navigation)
        if (growOnly && clamped <= st.columnWidth) return;
        if (st.columnWidth === clamped) return;
        st.columnWidth = clamped;
        this.emitter.fire(viewUri);
    }

    /** Width used for rendering. Defaults to DEFAULT_COLUMN_WIDTH; may be updated by setColumnWidth (e.g. from visibleRanges). */
    private getRenderWidth(state: ViewerState): number {
        return state.columnWidth;
    }

    async provideTextDocumentContent(uri: vscode.Uri): Promise<string> {
        const state = this.getOrInitState(uri);
        const header = await this.buildHeader(state);
        const body = await this.render(state);
        return `${header}\n\n${body}`;
    }

    private async buildHeader(state: ViewerState): Promise<string> {
        const fileName = state.fileUri.fsPath.split(/[/\\]/).pop() ?? 'file.jsonl';
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
            JSONL_TEXT_HEADER_ACTIONS.PREV,
            pad,
            JSONL_TEXT_HEADER_ACTIONS.NEXT,
            pad,
            JSONL_TEXT_HEADER_ACTIONS.SEARCH,
            pad,
            JSONL_TEXT_HEADER_ACTIONS.GOTO,
            sep,
            JSONL_TEXT_HEADER_ACTIONS.CARDS,
            pad,
            JSONL_TEXT_HEADER_ACTIONS.EDIT,
            pad,
            JSONL_TEXT_HEADER_ACTIONS.TOKENIZER,
            sep,
            rangeLabel,
            sep,
            searchLabel,
            sep,
            tokenizerLabel,
        ].join('');
        const renderWidth = this.getRenderWidth(state);
        const line0Padded = line0.padEnd(Math.max(line0.length, renderWidth), ' ');
        const rule = '═'.repeat(renderWidth);
        return ['', line0Padded, rule].join('\n');
    }

    private async render(state: ViewerState): Promise<string> {
        const records = await this.readPage(state);
        if (records.length === 0) {
            return '(no records to display)';
        }
        let tokenCounts: (number | null)[] | undefined;
        if (state.tokenizer) {
            tokenCounts = await Promise.all(
                records.map((r) =>
                    countTokens(r.raw, state.tokenizer!, 'auto')
                        .then((res) => res.count)
                        .catch(() => null)
                )
            );
        }
        return this.renderCards(state, records, tokenCounts);
    }

    private async readPage(state: ViewerState): Promise<Array<{ index: number; data: any | null; raw: string }>> {
        const records: Array<{ index: number; data: any | null; raw: string }> = [];
        const filePath = state.fileUri.fsPath;

        if (!fs.existsSync(filePath)) {
            return records;
        }

        const stream = fs.createReadStream(filePath, { encoding: 'utf8' });
        const rl = readline.createInterface({ input: stream });

        let lineNum = 0;
        const want = state.pageSize;
        const search = state.search?.toLowerCase() ?? null;

        try {
            for await (const line of rl) {
                const shouldSkipByLine = lineNum < state.startLine;
                lineNum++;

                if (shouldSkipByLine) {
                    continue;
                }

                if (records.length >= want) {
                    break;
                }

                if (search && !line.toLowerCase().includes(search)) {
                    continue;
                }

                let data: any | null = null;
                try {
                    data = JSON.parse(line);
                } catch {
                    data = null;
                }

                records.push({ index: lineNum - 1, data, raw: line });
            }
        } finally {
            rl.close();
            stream.destroy();
        }

        return records;
    }

    private renderCards(
        state: ViewerState,
        records: Array<{ index: number; data: any | null; raw: string }>,
        tokenCounts?: (number | null)[]
    ): string {
        const width = this.getRenderWidth(state);
        const innerWidth = width - 2;
        const contentWidth = innerWidth - 2 * CARD_PAD_H;
        const boxes: string[] = [];
        const hor = '─'.repeat(innerWidth);
        const top = '┌' + hor + '┐';
        const bottom = '└' + hor + '┘';
        const sep = '├' + hor + '┤';
        const padSide = ' '.repeat(CARD_PAD_H);
        const emptyLine = '│' + ' '.repeat(innerWidth) + '│';

        for (let i = 0; i < records.length; i++) {
            const rec = records[i];
            const tokenStr =
                tokenCounts && tokenCounts[i] !== null
                    ? `  (${(tokenCounts[i] as number).toLocaleString()} tokens)`
                    : tokenCounts
                      ? '  (— tokens)'
                      : '';
            const header = `  [#${rec.index}]  ${tokenStr}  `.trimEnd();

            const bodyLines: string[] = [];
            if (rec.data && typeof rec.data === 'object') {
                const entries = Object.entries(rec.data).slice(0, 15);
                for (const [key, value] of entries) {
                    if (value !== null && typeof value === 'object') {
                        bodyLines.push(this.padLine(`  ${key}:`, contentWidth));
                        for (const line of this.prettyValueLines(value, contentWidth - 4)) {
                            bodyLines.push(this.padLine('    ' + line.trimEnd(), contentWidth));
                        }
                    } else {
                        const line = `  ${key}: ${this.formatValueOneLine(value)}`;
                        bodyLines.push(this.padLine(this.truncateAtWord(line, contentWidth), contentWidth));
                    }
                }
            } else {
                bodyLines.push(this.padLine(this.truncateAtWord('  ' + rec.raw, contentWidth), contentWidth));
            }

            const headerPadded = this.padLine(this.truncateAtWord(header, contentWidth), contentWidth);
            const contentRow = (line: string) => '│' + padSide + line + padSide + '│';
            const verticalPadding = Array(CARD_PAD_V).fill(emptyLine);
            const boxLines = [
                top,
                contentRow(headerPadded),
                sep,
                ...verticalPadding,
                ...bodyLines.map((l) => contentRow(l)),
                ...verticalPadding,
                bottom,
            ];
            boxes.push(boxLines.join('\n'));
        }
        return boxes.join('\n\n');
    }

    /** Pretty-print JSON (reuses built-in; same idea as webview pretty view). */
    private prettyPrintJson(value: unknown): string {
        try {
            return JSON.stringify(value, null, 2);
        } catch {
            return String(value);
        }
    }

    /** Format a value for single-line display. */
    private formatValueOneLine(value: unknown): string {
        if (value === null) return 'null';
        if (typeof value !== 'object') return String(value);
        try {
            return JSON.stringify(value);
        } catch {
            return String(value);
        }
    }

    /** Pretty-printed lines for an object value; each line fits within maxWidth (wrap at word boundaries). */
    private prettyValueLines(value: unknown, maxWidth: number): string[] {
        const raw = this.prettyPrintJson(value);
        const lines: string[] = [];
        for (const line of raw.split(/\r?\n/)) {
            if (line.length <= maxWidth) {
                lines.push(this.padLine(line, maxWidth));
            } else {
                lines.push(...this.wrapAtWords(line, maxWidth));
            }
        }
        return lines;
    }

    /** Wrap text at word boundaries so words don't split across lines. */
    private wrapAtWords(text: string, maxWidth: number): string[] {
        const result: string[] = [];
        let remaining = text;
        while (remaining.length > 0) {
            if (remaining.length <= maxWidth) {
                result.push(this.padLine(remaining, maxWidth));
                break;
            }
            const chunk = remaining.slice(0, maxWidth + 1);
            const lastSpace = chunk.lastIndexOf(' ');
            const breakAt =
                lastSpace > 0 ? lastSpace : maxWidth;
            result.push(this.padLine(remaining.slice(0, breakAt), maxWidth));
            remaining = remaining.slice(breakAt).replace(/^\s+/, '');
        }
        return result;
    }

    /** Truncate at last word boundary before width to avoid mid-word cut. */
    private truncateAtWord(text: string, width: number): string {
        if (text.length <= width) return text;
        const slice = text.slice(0, width + 1);
        const lastSpace = slice.lastIndexOf(' ');
        if (lastSpace > width * 0.6) return text.slice(0, lastSpace);
        return text.slice(0, width);
    }

    private padLine(text: string, width: number): string {
        if (text.length >= width) {
            return text.slice(0, width);
        }
        return text + ' '.repeat(width - text.length);
    }

}

