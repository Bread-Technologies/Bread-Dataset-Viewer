import * as fs from 'fs';
import * as readline from 'readline';
import csvParser = require('csv-parser');
import {
    IDataLoader,
    FileMetadata,
    RowBatch,
    DataRow,
    FilterOptions,
    SchemaInfo,
    ColumnInfo,
    DataType
} from '../interfaces';

/**
 * CsvDataLoader - Memory-efficient streaming loader for CSV and TSV files
 *
 * Key Features:
 * - Automatic delimiter detection (comma, tab, semicolon, pipe)
 * - Streaming I/O for 100GB+ file support
 * - Handles quoted fields with embedded delimiters
 * - Handles escaped quotes (both "" and \")
 * - Zero-based row indexing
 * - Search filtering without full file scan
 */
export class CsvDataLoader implements IDataLoader {
    private filePath: string = '';
    private fileSizeBytes: number = 0;
    private delimiter: string = ',';
    private headers: string[] = [];
    private totalRows?: number; // Optional - unknown until full scan

    /**
     * Initialize the loader by detecting delimiter and reading headers
     *
     * @param filePath Absolute path to CSV/TSV file
     */
    async initialize(filePath: string): Promise<void> {
        this.filePath = filePath;

        // Get file stats
        const stats = await fs.promises.stat(filePath);
        this.fileSizeBytes = stats.size;

        // Detect delimiter by analyzing first few lines
        this.delimiter = await this.detectDelimiter(filePath);

        // Read headers from first row
        this.headers = await this.readHeaders(filePath, this.delimiter);
    }

    /**
     * Get file metadata including format and schema
     */
    async getMetadata(): Promise<FileMetadata> {
        const format = this.delimiter === '\t' ? 'tsv' : 'csv';

        const columns: ColumnInfo[] = this.headers.map(name => ({
            name,
            type: DataType.STRING, // CSV doesn't have type information
            nullable: true
        }));

        const schema: SchemaInfo = { columns };

        return {
            format,
            fileSizeBytes: this.fileSizeBytes,
            totalRows: this.totalRows,
            schema
        };
    }

    /**
     * Load a batch of rows with streaming support
     *
     * @param offset Zero-based row offset (excluding header)
     * @param limit Maximum number of rows to load
     * @param filter Optional search filter
     * @returns Batch of rows with hasMore flag
     */
    async loadRows(offset: number, limit: number, filter?: FilterOptions): Promise<RowBatch> {
        return new Promise((resolve, reject) => {
            const rows: DataRow[] = [];
            let currentIndex = 0;
            const searchTerm = filter?.searchTerm?.toLowerCase();
            let resolved = false;

            const stream = fs.createReadStream(this.filePath);
            const parser = csvParser({
                separator: this.delimiter
                // Let csv-parser read headers from first row automatically
            });

            const cleanup = () => {
                if (!resolved) {
                    resolved = true;
                    resolve({
                        rows,
                        hasMore: rows.length === limit,
                        nextOffset: currentIndex
                    });
                }
            };

            stream
                .pipe(parser)
                .on('data', (row: any) => {
                    // Skip rows before offset
                    if (currentIndex < offset) {
                        currentIndex++;
                        return;
                    }

                    // Stop if we have enough rows
                    if (rows.length >= limit) {
                        stream.destroy();
                        cleanup();
                        return;
                    }

                    // Apply search filter if provided
                    if (searchTerm) {
                        const rowText = JSON.stringify(row).toLowerCase();
                        if (!rowText.includes(searchTerm)) {
                            currentIndex++;
                            return;
                        }
                    }

                    rows.push({
                        index: currentIndex,
                        data: this.normalizeCsvRecord(row),
                        raw: this.rowToCSVLine(row)
                    });

                    currentIndex++;
                })
                .on('end', () => {
                    // Update total rows if we reached the end
                    if (rows.length < limit) {
                        this.totalRows = currentIndex;
                    }
                    cleanup();
                })
                .on('error', (error: Error) => {
                    if (!resolved) {
                        resolved = true;
                        stream.destroy();
                        reject(error);
                    }
                });
        });
    }

    /**
     * Jump to a specific row and load a batch from that point
     *
     * @param rowNumber Zero-based row number to jump to
     * @returns Batch of rows starting from the specified row
     */
    async jumpToRow(rowNumber: number): Promise<RowBatch> {
        return this.loadRows(rowNumber, 100);
    }

    /**
     * Extract text representation for token counting
     *
     * @param row Row data (object or string)
     * @returns JSON string representation
     */
    extractTextForTokens(row: any): string {
        if (typeof row === 'string') {
            return row;
        }
        return JSON.stringify(row);
    }

    /**
     * Detect delimiter by analyzing first few lines
     * Tests comma, tab, semicolon, and pipe
     *
     * Strategy:
     * 1. Read first 5 lines
     * 2. Try each delimiter
     * 3. Choose delimiter with:
     *    - Consistent column count across lines
     *    - Most columns (> 1)
     * 4. Fallback to comma if no clear winner
     */
    private async detectDelimiter(filePath: string): Promise<string> {
        const delimiters = [',', '\t', ';', '|'];
        const sampleLines: string[] = [];

        // Read first 5 lines
        const rl = readline.createInterface({
            input: fs.createReadStream(filePath),
            crlfDelay: Infinity
        });

        for await (const line of rl) {
            sampleLines.push(line);
            if (sampleLines.length >= 5) {
                rl.close();
                break;
            }
        }

        if (sampleLines.length === 0) {
            return ','; // Default to comma for empty files
        }

        // Score each delimiter
        let bestDelimiter = ',';
        let bestScore = -1;

        for (const delimiter of delimiters) {
            const counts = sampleLines.map(line => this.countColumns(line, delimiter));

            // Check if column count is consistent
            const firstCount = counts[0];
            const isConsistent = counts.every(count => count === firstCount);

            if (isConsistent && firstCount > 1) {
                const score = firstCount;
                if (score > bestScore) {
                    bestScore = score;
                    bestDelimiter = delimiter;
                }
            }
        }

        return bestDelimiter;
    }

    /**
     * Count columns in a line for a given delimiter
     * Handles quoted fields properly
     */
    private countColumns(line: string, delimiter: string): number {
        let count = 1;
        let inQuotes = false;

        for (let i = 0; i < line.length; i++) {
            const char = line[i];

            if (char === '"') {
                // Handle escaped quotes ("")
                if (i + 1 < line.length && line[i + 1] === '"') {
                    i++; // Skip next quote
                } else {
                    inQuotes = !inQuotes;
                }
            } else if (char === delimiter && !inQuotes) {
                count++;
            }
        }

        return count;
    }

    /**
     * Read headers from first row
     */
    private async readHeaders(filePath: string, delimiter: string): Promise<string[]> {
        return new Promise((resolve, reject) => {
            const rl = readline.createInterface({
                input: fs.createReadStream(filePath),
                crlfDelay: Infinity
            });

            rl.on('line', (line: string) => {
                // Parse the first line as headers
                const headers = this.parseCSVLine(line, delimiter);
                rl.close();
                resolve(headers);
            });

            rl.on('error', (error: Error) => {
                rl.close();
                reject(error);
            });
        });
    }

    /**
     * Parse a CSV line respecting quotes
     */
    private parseCSVLine(line: string, delimiter: string): string[] {
        const result: string[] = [];
        let current = '';
        let inQuotes = false;

        for (let i = 0; i < line.length; i++) {
            const char = line[i];

            if (char === '"') {
                // Handle escaped quotes ("")
                if (i + 1 < line.length && line[i + 1] === '"') {
                    current += '"';
                    i++; // Skip next quote
                } else {
                    inQuotes = !inQuotes;
                }
            } else if (char === delimiter && !inQuotes) {
                result.push(current.trim());
                current = '';
            } else {
                current += char;
            }
        }

        // Add last field
        result.push(current.trim());

        return result;
    }

    /**
     * Convert row object back to CSV line for raw view
     */
    private rowToCSVLine(row: any): string {
        const values = this.headers.map(header => {
            const value = row[header];
            if (value === null || value === undefined) {
                return '';
            }

            const strValue = String(value);

            // Quote if contains delimiter, quotes, or newlines
            if (strValue.includes(this.delimiter) || strValue.includes('"') || strValue.includes('\n')) {
                return `"${strValue.replace(/"/g, '""')}"`;
            }

            return strValue;
        });

        return values.join(this.delimiter);
    }

    /**
     * Normalize CSV record by parsing JSON strings in fields
     *
     * CSV stores everything as strings, but fields may contain JSON data
     * (e.g., messages field with chat format). This attempts to parse
     * string values that look like JSON arrays or objects.
     */
    private normalizeCsvRecord(record: any): any {
        if (record === null || record === undefined) {
            return record;
        }

        if (typeof record !== 'object') {
            return record;
        }

        const normalized: any = {};
        for (const key of Object.keys(record)) {
            const value = record[key];

            if (typeof value === 'string') {
                // Try to parse JSON strings (arrays or objects)
                const trimmed = value.trim();
                if ((trimmed.startsWith('[') && trimmed.endsWith(']')) ||
                    (trimmed.startsWith('{') && trimmed.endsWith('}'))) {
                    try {
                        normalized[key] = JSON.parse(trimmed);
                    } catch {
                        // Not valid JSON, keep as string
                        normalized[key] = value;
                    }
                } else {
                    normalized[key] = value;
                }
            } else {
                normalized[key] = value;
            }
        }

        return normalized;
    }

    /**
     * Clean up resources
     */
    dispose(): void {
        // No persistent resources to clean up
        // Streams are closed after each operation
    }
}
