import * as vscode from 'vscode';
import { ITextDecorator } from './ITextDecorator';

/**
 * Decorator for CSV/TSV formats
 * Highlights table structure (header row, separators, cell values)
 */
export class CsvDecorator implements ITextDecorator {
    getDecorationRanges(document: vscode.TextDocument): Map<string, vscode.Range[]> {
        const headerRanges: vscode.Range[] = [];
        const separatorRanges: vscode.Range[] = [];
        const numberRanges: vscode.Range[] = [];
        const stringRanges: vscode.Range[] = [];

        const headerEnd = 3; // Skip header (blank, header line, rule)

        // Find table header row (first data row after header)
        if (document.lineCount > headerEnd + 1) {
            const headerLine = headerEnd + 1; // Line after ┌──┐ border
            const headerText = document.lineAt(headerLine).text;
            if (headerText.includes('│')) {
                // Highlight entire header row
                headerRanges.push(new vscode.Range(headerLine, 0, headerLine, headerText.length));
            }
        }

        // Process all lines for separators and cell values
        for (let i = headerEnd; i < document.lineCount; i++) {
            const line = document.lineAt(i);
            const text = line.text;

            // Find separator characters
            for (let j = 0; j < text.length; j++) {
                const char = text[j];
                if ('│├┤┬┴┼─┌┐└┘'.includes(char)) {
                    separatorRanges.push(new vscode.Range(i, j, i, j + 1));
                }
            }

            // Skip header row, top border, header separator for cell coloring
            if (i <= headerEnd + 2) continue;

            // Split line by │ to get cell contents
            const cells = text.split('│').slice(1, -1); // Remove first and last empty elements
            let currentPos = text.indexOf('│') + 1;

            for (const cell of cells) {
                const trimmed = cell.trim();
                if (trimmed.length > 0 && trimmed !== '...' && !trimmed.match(/^[─┌┐└┘├┤┬┴┼]+$/)) {
                    // Check if it's a number
                    if (/^-?\d+(\.\d+)?$/.test(trimmed)) {
                        // Find the actual position of the number (not the padded cell)
                        const numStart = currentPos + cell.indexOf(trimmed);
                        numberRanges.push(new vscode.Range(i, numStart, i, numStart + trimmed.length));
                    } else if (trimmed !== 'null' && trimmed !== 'undefined') {
                        // It's a string value
                        const strStart = currentPos + cell.indexOf(trimmed);
                        stringRanges.push(new vscode.Range(i, strStart, i, strStart + trimmed.length));
                    }
                }
                currentPos += cell.length + 1; // +1 for the │ separator
            }
        }

        const map = new Map<string, vscode.Range[]>();
        map.set('header', headerRanges);
        map.set('separator', separatorRanges);
        map.set('number', numberRanges);
        map.set('string', stringRanges);
        return map;
    }

    createDecorationTypes(): Map<string, vscode.TextEditorDecorationType> {
        return new Map([
            ['header', vscode.window.createTextEditorDecorationType({
                fontWeight: 'bold',
                color: new vscode.ThemeColor('terminal.ansiCyan'),
            })],
            ['separator', vscode.window.createTextEditorDecorationType({
                color: new vscode.ThemeColor('editorLineNumber.activeForeground'),
            })],
            ['number', vscode.window.createTextEditorDecorationType({
                color: new vscode.ThemeColor('terminal.ansiGreen'),
            })],
            ['string', vscode.window.createTextEditorDecorationType({
                color: new vscode.ThemeColor('terminal.ansiYellow'),
            })],
        ]);
    }
}
