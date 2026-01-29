import * as fs from 'fs';
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
 * Data loader for standard JSON files
 *
 * Supports two root structures:
 * - Single object: {"key": "value"} → Treated as 1 row
 * - Array of objects: [{...}, {...}] → Each element is a row
 *
 * Note: Unlike JSONL, JSON files are loaded entirely into memory.
 * This is acceptable since JSON files are typically smaller than
 * streaming formats like JSONL (which can be 100GB+).
 */
export class JsonDataLoader implements IDataLoader {
    private filePath: string = '';
    private fileSizeBytes: number = 0;
    private data: any[] = [];
    private isArray: boolean = false;

    /**
     * Initialize the loader with a JSON file path
     * Reads and parses the entire file, normalizing to array format
     */
    async initialize(filePath: string): Promise<void> {
        this.filePath = filePath;

        // Get file stats
        const stats = await fs.promises.stat(filePath);
        this.fileSizeBytes = stats.size;

        // Read entire JSON file
        const content = await fs.promises.readFile(filePath, 'utf8');

        // Parse JSON
        const parsed = JSON.parse(content);

        // Normalize to array format
        if (Array.isArray(parsed)) {
            this.data = parsed;
            this.isArray = true;
        } else if (parsed !== null && typeof parsed === 'object') {
            // Single object - wrap in array
            this.data = [parsed];
            this.isArray = false;
        } else {
            // Primitive value - wrap in object then array
            this.data = [{ value: parsed }];
            this.isArray = false;
        }
    }

    /**
     * Get metadata about the JSON file
     * Includes schema extracted from first object's keys
     */
    async getMetadata(): Promise<FileMetadata> {
        const schema = this.extractSchema();

        return {
            format: 'json',
            fileSizeBytes: this.fileSizeBytes,
            totalRows: this.data.length,
            schema
        };
    }

    /**
     * Load a batch of rows from the parsed JSON data
     *
     * @param offset Starting row number (zero-based)
     * @param limit Maximum number of rows to load
     * @param filter Optional filter options (search term)
     * @returns Batch of rows with pagination info
     */
    async loadRows(offset: number, limit: number, filter?: FilterOptions): Promise<RowBatch> {
        const rows: DataRow[] = [];
        const searchTerm = filter?.searchTerm?.toLowerCase();

        // Check bounds
        if (offset >= this.data.length) {
            return { rows: [], hasMore: false, nextOffset: this.data.length };
        }

        let collected = 0;
        let currentIndex = offset;

        while (currentIndex < this.data.length && collected < limit) {
            const item = this.data[currentIndex];

            // Apply search filter if present
            if (searchTerm) {
                const rowText = JSON.stringify(item).toLowerCase();
                if (!rowText.includes(searchTerm)) {
                    currentIndex++;
                    continue;
                }
            }

            rows.push({
                index: currentIndex,
                data: item,
                raw: JSON.stringify(item)
            });

            collected++;
            currentIndex++;
        }

        return {
            rows,
            hasMore: currentIndex < this.data.length,
            nextOffset: currentIndex
        };
    }

    /**
     * Jump to a specific row and load a batch from that point
     *
     * @param rowNumber Row number to jump to (zero-based)
     * @returns Batch of rows starting from the specified row
     */
    async jumpToRow(rowNumber: number): Promise<RowBatch> {
        return this.loadRows(rowNumber, 100);
    }

    /**
     * Extract text from a row for token counting
     *
     * @param row Row data object
     * @returns JSON string for token counting
     */
    extractTextForTokens(row: any): string {
        if (typeof row === 'string') {
            return row;
        }
        return JSON.stringify(row);
    }

    /**
     * Extract schema information from the first object
     */
    private extractSchema(): SchemaInfo {
        if (this.data.length === 0) {
            return { columns: [] };
        }

        const firstRow = this.data[0];
        if (!firstRow || typeof firstRow !== 'object' || Array.isArray(firstRow)) {
            return { columns: [] };
        }

        const columns: ColumnInfo[] = Object.entries(firstRow).map(([key, value]) => ({
            name: key,
            type: this.inferType(value),
            nullable: value === null
        }));

        return { columns };
    }

    /**
     * Infer DataType from a JavaScript value
     */
    private inferType(value: any): DataType {
        if (value === null) return DataType.NULL;
        if (Array.isArray(value)) return DataType.ARRAY;
        if (typeof value === 'boolean') return DataType.BOOLEAN;
        if (typeof value === 'number') {
            return Number.isInteger(value) ? DataType.INTEGER : DataType.NUMBER;
        }
        if (typeof value === 'string') return DataType.STRING;
        if (typeof value === 'object') return DataType.OBJECT;
        return DataType.STRING;
    }

    /**
     * Clean up resources
     */
    dispose(): void {
        // Clear data array to free memory
        this.data = [];
    }
}
