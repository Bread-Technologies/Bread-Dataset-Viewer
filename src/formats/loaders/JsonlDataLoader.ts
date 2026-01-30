import * as fs from 'fs';
import * as readline from 'readline';
import {
    IDataLoader,
    FileMetadata,
    RowBatch,
    DataRow,
    FilterOptions
} from '../interfaces';

/**
 * Data loader for JSONL (JSON Lines) files
 *
 * Critical Requirements:
 * - Streaming-first: Uses fs.createReadStream() + readline (no readFile())
 * - Memory-efficient: Supports 100GB+ files by loading in batches
 * - Zero-based indexing: Line numbers start at 0
 * - Error handling: Gracefully handles malformed JSON lines
 */
export class JsonlDataLoader implements IDataLoader {
    private filePath: string = '';
    private fileSizeBytes: number = 0;

    /**
     * Initialize the loader with a file path
     */
    async initialize(filePath: string): Promise<void> {
        this.filePath = filePath;

        // Get file stats for metadata
        const stats = await fs.promises.stat(filePath);
        this.fileSizeBytes = stats.size;
    }

    /**
     * Get metadata about the JSONL file
     */
    async getMetadata(): Promise<FileMetadata> {
        return {
            format: 'jsonl',
            fileSizeBytes: this.fileSizeBytes,
            // Note: totalRows not provided - would require scanning entire file
        };
    }

    /**
     * Load a batch of rows from the JSONL file
     * Uses streaming to support 100GB+ files
     *
     * @param offset Starting line number (zero-based)
     * @param limit Maximum number of rows to load
     * @param filter Optional filter options (search term, selected paths)
     * @returns Batch of rows with pagination info
     */
    async loadRows(offset: number, limit: number, filter?: FilterOptions): Promise<RowBatch> {
        const stream = fs.createReadStream(this.filePath, { encoding: 'utf8' });
        const rl = readline.createInterface({ input: stream });

        let lineNum = 0; // Zero-based indexing
        const rows: DataRow[] = [];
        const searchTerm = filter?.searchTerm;

        try {
            for await (const line of rl) {
                // Skip lines before offset
                if (lineNum < offset) {
                    lineNum++;
                    continue;
                }

                // Stop if we have enough rows
                if (rows.length >= limit) {
                    break;
                }

                // Apply search filter if present (case-insensitive)
                if (searchTerm && !line.toLowerCase().includes(searchTerm.toLowerCase())) {
                    lineNum++;
                    continue;
                }

                // Parse JSON with error handling
                try {
                    const data = JSON.parse(line);
                    rows.push({ index: lineNum, data, raw: line });
                } catch {
                    // Handle malformed JSON - include line with error flag
                    rows.push({
                        index: lineNum,
                        data: null,
                        raw: line,
                        error: 'Invalid JSON'
                    });
                }

                lineNum++;
            }

            return {
                rows,
                hasMore: rows.length === limit,
                nextOffset: lineNum
            };
        } finally {
            // Always close streams to prevent memory leaks
            rl.close();
            stream.destroy();
        }
    }

    /**
     * Jump to a specific row and load a batch from that point
     *
     * @param rowNumber Row number to jump to (zero-based)
     * @returns Batch of rows starting from the specified row
     */
    async jumpToRow(rowNumber: number): Promise<RowBatch> {
        // Simply delegate to loadRows with the row number as offset
        return this.loadRows(rowNumber, 100);
    }

    /**
     * Extract text from a row for token counting
     * For JSONL, we use the raw JSON string
     *
     * @param row Row data object
     * @returns Raw JSON string for token counting
     */
    extractTextForTokens(row: any): string {
        if (typeof row === 'string') {
            return row;
        }
        return JSON.stringify(row);
    }

    /**
     * Clean up resources
     * No persistent streams to clean up for JSONL loader
     */
    dispose(): void {
        // No cleanup needed - streams are closed after each operation
    }
}
