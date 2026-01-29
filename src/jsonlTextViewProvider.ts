import * as vscode from 'vscode';
import * as fs from 'fs';
import * as readline from 'readline';

type ViewMode = 'cards' | 'table' | 'raw';

interface ViewerState {
    fileUri: vscode.Uri;
    viewMode: ViewMode;
    startLine: number;
    pageSize: number;
    filter: string | null;
}

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

    private fromViewUri(viewUri: vscode.Uri): vscode.Uri {
        const encoded = viewUri.path.replace(/^\//, '');
        const decoded = decodeURIComponent(encoded);
        return vscode.Uri.parse(decoded);
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

    async provideTextDocumentContent(uri: vscode.Uri): Promise<string> {
        const state = this.getOrInitState(uri);
        const header = await this.buildHeader(state);
        const body = await this.render(state);
        return `${header}\n${body}`;
    }

    private async buildHeader(state: ViewerState): Promise<string> {
        const modeLabel = state.viewMode.toUpperCase();
        const filterLabel = state.filter ? `Filter: "${state.filter}"` : 'Filter: (none)';
        const rangeLabel = `Lines ${state.startLine}–${state.startLine + state.pageSize - 1}`;
        return [
            `JSONL Viewer (text) │ Mode: ${modeLabel} │ ${rangeLabel} │ ${filterLabel}`,
            '────────────────────────────────────────────────────────────────────────────────────',
        ].join('\n');
    }

    private async render(state: ViewerState): Promise<string> {
        const records = await this.readPage(state);
        if (records.length === 0) {
            return '(no records to display)';
        }
        switch (state.viewMode) {
            case 'cards':
                return this.renderCards(records);
            case 'table':
                return this.renderTable(records);
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

    private renderCards(records: Array<{ index: number; data: any | null; raw: string }>): string {
        const boxes: string[] = [];
        for (const rec of records) {
            const summary = this.buildSummary(rec);
            const header = `[#${rec.index}] ${summary}`;
            const width = Math.min(Math.max(header.length + 4, 40), 100);
            const top = '╭' + '─'.repeat(width - 2) + '╮';
            const bottom = '╰' + '─'.repeat(width - 2) + '╯';

            const bodyLines: string[] = [];

            if (rec.data && typeof rec.data === 'object') {
                const entries = Object.entries(rec.data).slice(0, 10);
                for (const [key, value] of entries) {
                    const line = `${key}: ${String(value)}`;
                    bodyLines.push(this.padLine(line, width - 2));
                }
            } else {
                bodyLines.push(this.padLine(rec.raw, width - 2));
            }

            const headerPadded = this.padLine(header, width - 2);
            const boxLines = [
                top,
                `│${headerPadded}│`,
                ...bodyLines.map(l => `│${l}│`),
                bottom,
            ];
            boxes.push(boxLines.join('\n'));
        }
        return boxes.join('\n\n');
    }

    private renderTable(records: Array<{ index: number; data: any | null; raw: string }>): string {
        const maxCols = 6;
        const colWidth = 20;

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

        const headerRow = headers
            .map(h => this.truncateCell(h, colWidth))
            .join(' │ ');
        const sepRow = headers
            .map(() => '─'.repeat(colWidth))
            .join('─┼─');

        const rows: string[] = [];
        for (const rec of records) {
            const cols: string[] = [];
            cols.push(this.truncateCell(String(rec.index), colWidth));

            for (const key of keys) {
                let value = '';
                if (rec.data && typeof rec.data === 'object' && key in rec.data) {
                    value = String((rec.data as any)[key]);
                }
                cols.push(this.truncateCell(value, colWidth));
            }

            rows.push(cols.join(' │ '));
        }

        return [headerRow, sepRow, ...rows].join('\n');
    }

    private renderRaw(records: Array<{ index: number; data: any | null; raw: string }>): string {
        const chunks: string[] = [];
        for (const rec of records) {
            chunks.push(`L${rec.index}:\n${rec.raw}\n`);
        }
        return chunks.join('\n');
    }

    private buildSummary(rec: { index: number; data: any | null; raw: string }): string {
        if (rec.data && typeof rec.data === 'object') {
            const anyData = rec.data as any;
            if (typeof anyData.message === 'string') {
                return this.truncateText(anyData.message, 60);
            }
        }
        return this.truncateText(rec.raw, 60);
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

