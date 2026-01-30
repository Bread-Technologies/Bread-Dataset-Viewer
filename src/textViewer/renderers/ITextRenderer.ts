import { DataRow } from '../../formats/interfaces';

/**
 * Viewer state for text-based rendering
 */
export interface TextViewerState {
    fileUri: any; // vscode.Uri
    format: string;
    startLine: number;
    pageSize: number;
    search: string | null;
    tokenizer: string | null;
    columnWidth: number;
    mode: 'cards' | 'table' | 'raw';
}

/**
 * Interface for format-specific text renderers
 * Implementations provide format-appropriate layouts (cards for JSON, tables for CSV, etc.)
 */
export interface ITextRenderer {
    /**
     * Renders data rows as formatted text with box-drawing characters
     * @param rows - Data rows from the loader
     * @param state - Current viewer state (for column width, mode, etc.)
     * @param tokenCounts - Optional token counts per row
     * @returns Formatted text string ready for display
     */
    renderRows(
        rows: DataRow[],
        state: TextViewerState,
        tokenCounts?: (number | null)[]
    ): string;
}
