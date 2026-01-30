import { DataRow } from '../../formats/interfaces';
import { ITextRenderer, TextViewerState } from './ITextRenderer';

/** Horizontal padding (spaces) between card border and content. */
const CARD_PAD_H = 2;
/** Vertical padding: blank lines between card border and content. */
const CARD_PAD_V = 1;

/**
 * Renderer for JSON/JSONL formats
 * Displays data as card-based layout with key-value pairs
 */
export class JsonRenderer implements ITextRenderer {
    renderRows(
        rows: DataRow[],
        state: TextViewerState,
        tokenCounts?: (number | null)[]
    ): string {
        if (rows.length === 0) {
            return '(no records to display)';
        }

        // Use cards mode for JSON rendering
        return this.renderCards(rows, state.columnWidth, tokenCounts);
    }

    private renderCards(
        records: DataRow[],
        width: number,
        tokenCounts?: (number | null)[]
    ): string {
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
                // Handle non-object data (raw text or error)
                const displayText = rec.error ? `ERROR: ${rec.error}` : (rec.raw || String(rec.data));
                bodyLines.push(this.padLine(this.truncateAtWord('  ' + displayText, contentWidth), contentWidth));
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
