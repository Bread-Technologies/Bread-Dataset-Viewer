import * as vscode from 'vscode';
import * as fs from 'fs';
import * as readline from 'readline';

type ViewMode = 'cards' | 'table' | 'raw';

const DEFAULT_COLUMN_WIDTH = 80;
const MIN_COLUMN_WIDTH = 40;
const MAX_COLUMN_WIDTH = 500;

interface ViewerState {
    fileUri: vscode.Uri;
    viewMode: ViewMode;
    startLine: number;
    pageSize: number;
    filter: string | null;
    /** Visible editor width (chars); set from onDidChangeTextEditorVisibleRanges. */
    columnWidth: number;
}

/** Action labels in the header; DocumentLinkProvider turns these into command links. */
export const JSONL_TEXT_HEADER_ACTIONS = {
    NEXT: '[Next]',
    PREV: '[Prev]',
    FILTER: '[Filter]',
    GOTO: '[Goto]',
    CARDS: '[Cards]',
    TABLE: '[Table]',
    RAW: '[Raw]',
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
                filter: null,
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

    /** Update visible column width and refresh (call when editor is resized). */
    public setColumnWidth(viewUri: vscode.Uri, width: number): void {
        const clamped = Math.max(MIN_COLUMN_WIDTH, Math.min(MAX_COLUMN_WIDTH, Math.floor(width)));
        const st = this.getOrInitState(viewUri);
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
        const filterLabel = state.filter ? `Filter: "${state.filter}"` : 'Filter: (none)';
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
            JSONL_TEXT_HEADER_ACTIONS.FILTER,
            pad,
            JSONL_TEXT_HEADER_ACTIONS.GOTO,
            sep,
            JSONL_TEXT_HEADER_ACTIONS.CARDS,
            pad,
            JSONL_TEXT_HEADER_ACTIONS.TABLE,
            pad,
            JSONL_TEXT_HEADER_ACTIONS.RAW,
            sep,
            rangeLabel,
            sep,
            filterLabel,
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
        switch (state.viewMode) {
            case 'cards':
                return this.renderCards(state, records);
            case 'table':
                return this.renderTable(state, records);
            case 'raw':
            default:
                return this.renderRaw(records);
        }
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
        const filter = state.filter?.toLowerCase() ?? null;

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

                if (filter && !line.toLowerCase().includes(filter)) {
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

    private renderCards(state: ViewerState, records: Array<{ index: number; data: any | null; raw: string }>): string {
        const width = this.getRenderWidth(state);
        const innerWidth = width - 2;
        const boxes: string[] = [];
        const hor = '─'.repeat(innerWidth);
        const top = '┌' + hor + '┐';
        const bottom = '└' + hor + '┘';
        const sep = '├' + hor + '┤';

        for (const rec of records) {
            const prefix = `  [#${rec.index}]  `;
            const summaryMaxLen = Math.max(20, innerWidth - prefix.length);
            const summary = this.buildSummary(rec, summaryMaxLen);
            const header = prefix + summary;

            const bodyLines: string[] = [];
            if (rec.data && typeof rec.data === 'object') {
                const entries = Object.entries(rec.data).slice(0, 15);
                for (const [key, value] of entries) {
                    if (value !== null && typeof value === 'object') {
                        bodyLines.push(this.padLine(`  ${key}:`, innerWidth));
                        for (const line of this.prettyValueLines(value, innerWidth - 4)) {
                            bodyLines.push(this.padLine('    ' + line.trimEnd(), innerWidth));
                        }
                    } else {
                        const line = `  ${key}: ${this.formatValueOneLine(value)}`;
                        bodyLines.push(this.padLine(line, innerWidth));
                    }
                }
            } else {
                bodyLines.push(this.padLine('  ' + rec.raw, innerWidth));
            }

            const headerPadded = this.padLine(header, innerWidth);
            const boxLines = [
                top,
                '│' + headerPadded + '│',
                sep,
                ...bodyLines.map(l => '│' + this.padLine(l, innerWidth) + '│'),
                bottom,
            ];
            boxes.push(boxLines.join('\n'));
        }
        return boxes.join('\n\n');
    }

    private renderTable(state: ViewerState, records: Array<{ index: number; data: any | null; raw: string }>): string {
        const maxCols = 6;
        const keysSet = new Set<string>();
        for (const rec of records) {
            if (rec.data && typeof rec.data === 'object') {
                for (const key of Object.keys(rec.data)) {
                    keysSet.add(key);
                    if (keysSet.size >= maxCols - 1) break;
                }
            }
            if (keysSet.size >= maxCols - 1) break;
        }
        const keys = Array.from(keysSet);
        const headers = ['idx', ...keys];
        const numCols = headers.length;
        const totalWidth = this.getRenderWidth(state) - numCols - 1; // reserve one char per │ (including sides)
        const colWidth = Math.max(8, Math.floor(totalWidth / numCols));

        const hor = '─'.repeat(colWidth);
        const top = '┌' + Array(numCols).fill(hor).join('┬') + '┐';
        const headSep = '├' + Array(numCols).fill(hor).join('┼') + '┤';
        const bottom = '└' + Array(numCols).fill(hor).join('┴') + '┘';

        const headerCells = headers.map(h => this.truncateCell(h, colWidth));
        const headerRow = '│' + headerCells.join('│') + '│';

        const rows: string[] = [];
        for (const rec of records) {
            const cols: string[] = [];
            cols.push(this.truncateCell(String(rec.index), colWidth));
            for (const key of keys) {
                let value = '';
                if (rec.data && typeof rec.data === 'object' && key in rec.data) {
                    value = this.formatValueOneLine((rec.data as any)[key]);
                }
                cols.push(this.truncateCell(value, colWidth));
            }
            rows.push('│' + cols.join('│') + '│');
        }

        return [top, headerRow, headSep, ...rows, bottom].join('\n');
    }

    private renderRaw(records: Array<{ index: number; data: any | null; raw: string }>): string {
        const chunks: string[] = [];
        const sep = '─'.repeat(40);
        for (let i = 0; i < records.length; i++) {
            if (i > 0) chunks.push(sep);
            const rec = records[i];
            if (rec.data !== null && typeof rec.data === 'object') {
                chunks.push(`L${rec.index}:`, this.prettyPrintJson(rec.data));
            } else {
                chunks.push(`L${rec.index}:`, rec.raw);
            }
        }
        return chunks.join('\n');
    }

    private buildSummary(rec: { index: number; data: any | null; raw: string }, maxLen: number = 80): string {
        if (rec.data && typeof rec.data === 'object') {
            const anyData = rec.data as any;
            if (typeof anyData.message === 'string') {
                return this.truncateText(anyData.message, maxLen);
            }
        }
        return this.truncateText(rec.raw, maxLen);
    }

    /** Pretty-print JSON (reuses built-in; same idea as webview pretty view). */
    private prettyPrintJson(value: unknown): string {
        try {
            return JSON.stringify(value, null, 2);
        } catch {
            return String(value);
        }
    }

    /** Format a value for single-line display (e.g. table cell). */
    private formatValueOneLine(value: unknown): string {
        if (value === null) return 'null';
        if (typeof value !== 'object') return String(value);
        try {
            return JSON.stringify(value);
        } catch {
            return String(value);
        }
    }

    /** Pretty-printed lines for an object value; each line fits within maxWidth (wrap/truncate). */
    private prettyValueLines(value: unknown, maxWidth: number): string[] {
        const raw = this.prettyPrintJson(value);
        const lines: string[] = [];
        for (const line of raw.split(/\r?\n/)) {
            if (line.length <= maxWidth) {
                lines.push(this.padLine(line, maxWidth));
            } else {
                for (let i = 0; i < line.length; i += maxWidth) {
                    const chunk = line.slice(i, i + maxWidth);
                    lines.push(chunk.length < maxWidth ? this.padLine(chunk, maxWidth) : chunk);
                }
            }
        }
        return lines;
    }

    private padLine(text: string, width: number): string {
        if (text.length >= width) {
            return text.slice(0, width);
        }
        return text + ' '.repeat(width - text.length);
    }

    private truncateText(text: string, max: number): string {
        if (text.length <= max) return text;
        return text.slice(0, max - 1) + '…';
    }

    private truncateCell(text: string, max: number): string {
        if (text.length <= max) {
            return text.padEnd(max, ' ');
        }
        return text.slice(0, max - 1) + '…';
    }
}

