import * as vscode from 'vscode';

export type JsonlTokenType = 'key' | 'string' | 'number' | 'keyword';

interface TokenSpan {
    start: number;
    end: number;
    type: JsonlTokenType;
}

/** Result of tokenizing one line; inString is true if the line ended inside an unclosed string. */
function tokenizeLine(line: string): { spans: TokenSpan[]; inString: boolean } {
    const spans: TokenSpan[] = [];
    let i = 0;
    const n = line.length;
    let endedInString = false;

    while (i < n) {
        // Skip whitespace
        if (/\s/.test(line[i])) {
            i++;
            continue;
        }

        // Quoted key or string: "..." followed by optional space and :
        if (line[i] === '"') {
            const start = i;
            i++;
            while (i < n) {
                if (line[i] === '\\') i += 2;
                else if (line[i] === '"') { i++; break; }
                else i++;
            }
            const after = i;
            if (i >= n) {
                // No closing quote on this line — whole rest of line is string (wrapped/truncated)
                spans.push({ start, end: n, type: 'string' });
                endedInString = true;
                break;
            }
            while (i < n && line[i] === ' ') i++;
            if (i < n && line[i] === ':') {
                spans.push({ start, end: after, type: 'key' });
                i++;
                continue;
            }
            i = after;
            spans.push({ start, end: after, type: 'string' });
            continue;
        }

        // Number: -? \d+ (\.\d+)? ([eE][+-]?\d+)?
        const numMatch = line.slice(i).match(/^-?\d+(\.\d+)?([eE][+-]?\d+)?/);
        if (numMatch) {
            const len = numMatch[0].length;
            spans.push({ start: i, end: i + len, type: 'number' });
            i += len;
            continue;
        }

        // Keyword: true, false, null (word boundary)
        const wordMatch = line.slice(i).match(/^(true|false|null)\b/);
        if (wordMatch) {
            const len = wordMatch[0].length;
            spans.push({ start: i, end: i + len, type: 'keyword' });
            i += len;
            continue;
        }

        // Unquoted key: word characters until :
        const keyMatch = line.slice(i).match(/^([a-zA-Z_][a-zA-Z0-9_]*)\s*:/);
        if (keyMatch) {
            const keyLen = keyMatch[1].length;
            spans.push({ start: i, end: i + keyLen, type: 'key' });
            i += keyMatch[0].length;
            continue;
        }

        i++;
    }

    return { spans, inString: endedInString };
}

/** Card content lines in jsonl-view are "│  " + content + "  │" (CARD_PAD_H = 2). */
const CARD_PREFIX_LEN = 3;   // │ + 2 spaces
const CARD_SUFFIX_LEN = 3;   // 2 spaces + │

function isCardContentLine(text: string): boolean {
    return text.length >= CARD_PREFIX_LEN + CARD_SUFFIX_LEN
        && text.startsWith('│  ')
        && text.endsWith('  │');
}

/** Build decoration ranges from a jsonl-view document. Skips header (first 3 lines). */
export function getDecorationRanges(document: vscode.TextDocument): Map<JsonlTokenType, vscode.Range[]> {
    const keyRanges: vscode.Range[] = [];
    const stringRanges: vscode.Range[] = [];
    const numberRanges: vscode.Range[] = [];
    const keywordRanges: vscode.Range[] = [];

    const headerEnd = 3; // blank, header line, rule
    let inString = false;

    for (let lineIdx = headerEnd; lineIdx < document.lineCount; lineIdx++) {
        const line = document.lineAt(lineIdx);
        const text = line.text;

        let content: string;
        let offset: number;
        if (isCardContentLine(text)) {
            content = text.slice(CARD_PREFIX_LEN, text.length - CARD_SUFFIX_LEN);
            offset = CARD_PREFIX_LEN;
        } else {
            content = text;
            offset = 0;
        }

        if (inString) {
            // Continuation of a wrapped string: content is string until we see closing "
            let j = 0;
            let foundClose = false;
            while (j < content.length) {
                if (content[j] === '\\') j += 2;
                else if (content[j] === '"') { j++; foundClose = true; break; }
                else j++;
            }
            const endCol = foundClose ? offset + j : offset + content.length;
            stringRanges.push(new vscode.Range(lineIdx, offset, lineIdx, endCol));
            inString = !foundClose;
            if (!inString) {
                // Rest of line may have more tokens; tokenize from j (within content)
                const rest = content.slice(j);
                const { spans, inString: nextIn } = tokenizeLine(rest);
                for (const { start, end, type } of spans) {
                    const range = new vscode.Range(lineIdx, offset + j + start, lineIdx, offset + j + end);
                    switch (type) {
                        case 'key': keyRanges.push(range); break;
                        case 'string': stringRanges.push(range); break;
                        case 'number': numberRanges.push(range); break;
                        case 'keyword': keywordRanges.push(range); break;
                    }
                }
                inString = nextIn;
            }
            continue;
        }

        const { spans, inString: nextIn } = tokenizeLine(content);
        inString = nextIn;
        for (const { start, end, type } of spans) {
            const range = new vscode.Range(lineIdx, offset + start, lineIdx, offset + end);
            switch (type) {
                case 'key': keyRanges.push(range); break;
                case 'string': stringRanges.push(range); break;
                case 'number': numberRanges.push(range); break;
                case 'keyword': keywordRanges.push(range); break;
            }
        }
    }

    const map = new Map<JsonlTokenType, vscode.Range[]>();
    map.set('key', keyRanges);
    map.set('string', stringRanges);
    map.set('number', numberRanges);
    map.set('keyword', keywordRanges);
    return map;
}

/** Decoration types using theme colors so they follow light/dark theme. */
export function createJsonlDecorationTypes(): Map<JsonlTokenType, vscode.TextEditorDecorationType> {
    return new Map([
        ['key', vscode.window.createTextEditorDecorationType({
            color: new vscode.ThemeColor('textLink.foreground'),
        })],
        ['string', vscode.window.createTextEditorDecorationType({
            color: new vscode.ThemeColor('charts.green'),
        })],
        ['number', vscode.window.createTextEditorDecorationType({
            color: new vscode.ThemeColor('charts.blue'),
        })],
        ['keyword', vscode.window.createTextEditorDecorationType({
            color: new vscode.ThemeColor('descriptionForeground'),
        })],
    ]);
}

export function applyJsonlDecorations(
    editor: vscode.TextEditor,
    decorationTypes: Map<JsonlTokenType, vscode.TextEditorDecorationType>
): void {
    if (editor.document.uri.scheme !== 'jsonl-view') return;
    if (editor.document.lineCount <= 3) return;

    const rangesByType = getDecorationRanges(editor.document);
    decorationTypes.forEach((decorationType, tokenType) => {
        const ranges = rangesByType.get(tokenType) ?? [];
        editor.setDecorations(decorationType, ranges);
    });
}
