import { DataRow } from '../../formats/interfaces';
import { ITextRenderer, TextViewerState } from './ITextRenderer';

const MIN_COL_WIDTH = 8;
const BASE_MAX_COL_WIDTH = 40; // Base maximum for many columns

/**
 * Renderer for CSV/TSV formats
 * Displays data as a table with column headers
 */
export class CsvRenderer implements ITextRenderer {
    renderRows(
        rows: DataRow[],
        state: TextViewerState,
        tokenCounts?: (number | null)[]
    ): string {
        if (rows.length === 0) {
            return '(no records to display)';
        }

        // Extract columns from first row
        const firstData = rows[0].data;
        if (!firstData || typeof firstData !== 'object') {
            // Fallback: treat as simple text
            return rows.map((r, i) => {
                const tokenStr = tokenCounts?.[i] !== null && tokenCounts?.[i] !== undefined
                    ? ` (${tokenCounts[i]} tokens)`
                    : '';
                return `[#${r.index}]${tokenStr} ${r.raw || String(r.data)}`;
            }).join('\n');
        }

        const columns = Object.keys(firstData);
        const widths = this.calculateColumnWidths(rows, columns, state.columnWidth);

        // Render table
        const lines: string[] = [];

        // Top border
        lines.push(this.renderTableBorder(widths, 'top'));

        // Header row
        lines.push(this.renderTableRow(columns.map(c => c), widths, true));

        // Header separator
        lines.push(this.renderTableBorder(widths, 'middle'));

        // Data rows
        for (let i = 0; i < rows.length; i++) {
            const row = rows[i];
            const values = columns.map(col => this.formatCellValue(row.data[col]));
            lines.push(this.renderTableRow(values, widths, false));
        }

        // Bottom border
        lines.push(this.renderTableBorder(widths, 'bottom'));

        return lines.join('\n');
    }

    /**
     * Calculate optimal column widths based on content
     */
    private calculateColumnWidths(
        rows: DataRow[],
        columns: string[],
        maxTotalWidth: number
    ): number[] {
        const widths: number[] = [];
        const cellPadding = 2; // 1 space on each side
        const separators = (columns.length + 1); // │ separators

        // Calculate dynamic max column width based on number of columns
        // For few columns, allow them to be much wider
        const availableWidth = maxTotalWidth - separators;
        let maxColWidth: number;

        if (columns.length === 1) {
            maxColWidth = availableWidth - cellPadding; // Use almost all space for single column
        } else if (columns.length === 2) {
            maxColWidth = Math.floor(availableWidth / 2) - cellPadding; // Split between 2 columns
        } else if (columns.length <= 4) {
            maxColWidth = Math.min(BASE_MAX_COL_WIDTH * 3, Math.floor(availableWidth / columns.length));
        } else {
            maxColWidth = BASE_MAX_COL_WIDTH;
        }

        // Step 1: Start with column name length as minimum
        for (const col of columns) {
            widths.push(Math.max(col.length, MIN_COL_WIDTH) + cellPadding);
        }

        // Step 2: Sample first 20 rows to find max content width
        const sampleSize = Math.min(rows.length, 20);
        for (let i = 0; i < sampleSize; i++) {
            const row = rows[i].data;
            if (!row || typeof row !== 'object') continue;

            columns.forEach((col, idx) => {
                const value = this.formatCellValue(row[col]);
                widths[idx] = Math.max(widths[idx], value.length + cellPadding);
            });
        }

        // Step 3: Cap each column at dynamic max width (including padding)
        for (let i = 0; i < widths.length; i++) {
            widths[i] = Math.min(widths[i], maxColWidth + cellPadding);
        }

        // Step 4: If total exceeds max, proportionally reduce
        const totalWidth = widths.reduce((sum, w) => sum + w, 0) + separators;

        if (totalWidth > maxTotalWidth && columns.length > 0) {
            const scale = (maxTotalWidth - separators) / widths.reduce((sum, w) => sum + w, 0);
            for (let i = 0; i < widths.length; i++) {
                widths[i] = Math.max(MIN_COL_WIDTH + cellPadding, Math.floor(widths[i] * scale));
            }
        }

        return widths;
    }

    /**
     * Format a cell value as string, truncating if needed
     */
    private formatCellValue(value: unknown): string {
        if (value === null) return 'null';
        if (value === undefined) return '';
        if (typeof value === 'object') {
            try {
                return JSON.stringify(value);
            } catch {
                return String(value);
            }
        }
        return String(value);
    }

    /**
     * Render a table border (top, middle, or bottom)
     */
    private renderTableBorder(widths: number[], type: 'top' | 'middle' | 'bottom'): string {
        const parts: string[] = [];
        const left = type === 'top' ? '┌' : type === 'middle' ? '├' : '└';
        const right = type === 'top' ? '┐' : type === 'middle' ? '┤' : '┘';
        const join = type === 'top' ? '┬' : type === 'middle' ? '┼' : '┴';

        parts.push(left);
        for (let i = 0; i < widths.length; i++) {
            parts.push('─'.repeat(widths[i]));
            if (i < widths.length - 1) {
                parts.push(join);
            }
        }
        parts.push(right);

        return parts.join('');
    }

    /**
     * Render a table row (header or data)
     */
    private renderTableRow(values: string[], widths: number[], isHeader: boolean): string {
        const cells: string[] = [];
        const cellPadding = 1; // Add space on each side of cell content

        for (let i = 0; i < values.length; i++) {
            const width = widths[i];
            let value = values[i];

            // Account for padding in available width
            const availableWidth = width - (cellPadding * 2);

            // Truncate if too long
            if (value.length > availableWidth) {
                value = value.slice(0, availableWidth - 3) + '...';
            }

            // Pad to width with cell padding
            const padded = ' '.repeat(cellPadding) + value.padEnd(availableWidth, ' ') + ' '.repeat(cellPadding);
            cells.push(padded);
        }

        return '│' + cells.join('│') + '│';
    }
}
