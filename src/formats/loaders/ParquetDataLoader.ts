import * as fs from 'fs';
import * as parquet from '@dsnp/parquetjs';
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
 * Data loader for Parquet files using @dsnp/parquetjs
 *
 * Critical Requirements:
 * - Streaming-first: Uses ParquetReader with cursor-based pagination
 * - Memory-efficient: Supports 100GB+ files through row-by-row reading
 * - Schema extraction: Provides column names and types
 * - Zero-based indexing: Row numbers start at 0
 */
export class ParquetDataLoader implements IDataLoader {
    private filePath: string = '';
    private fileSizeBytes: number = 0;
    private reader?: parquet.ParquetReader;
    private schema?: parquet.ParquetSchema;
    private totalRows: number = 0;

    /**
     * Initialize the loader with a Parquet file path
     * Opens the Parquet file and reads metadata
     */
    async initialize(filePath: string): Promise<void> {
        this.filePath = filePath;

        // Get file stats for metadata
        const stats = await fs.promises.stat(filePath);
        this.fileSizeBytes = stats.size;

        // Open Parquet file
        this.reader = await parquet.ParquetReader.openFile(filePath);
        this.schema = this.reader.getSchema();
        this.totalRows = Number(this.reader.getRowCount());
    }

    /**
     * Get metadata about the Parquet file
     * Includes schema information with column names and types
     */
    async getMetadata(): Promise<FileMetadata> {
        if (!this.schema) {
            throw new Error('ParquetDataLoader not initialized. Call initialize() first.');
        }

        const schema = this.extractSchemaInfo();

        return {
            format: 'parquet',
            fileSizeBytes: this.fileSizeBytes,
            totalRows: this.totalRows,
            schema
        };
    }

    /**
     * Load a batch of rows from the Parquet file
     * Uses cursor-based streaming for memory efficiency
     *
     * @param offset Starting row number (zero-based)
     * @param limit Maximum number of rows to load
     * @param filter Optional filter options (search term)
     * @returns Batch of rows with pagination info
     */
    async loadRows(offset: number, limit: number, filter?: FilterOptions): Promise<RowBatch> {
        if (!this.reader) {
            throw new Error('ParquetDataLoader not initialized. Call initialize() first.');
        }

        const rows: DataRow[] = [];
        const searchTerm = filter?.searchTerm?.toLowerCase();

        // Check bounds
        if (offset >= this.totalRows) {
            return { rows: [], hasMore: false, nextOffset: this.totalRows };
        }

        // Create cursor for streaming reads
        const cursor = this.reader.getCursor();

        try {
            let currentIndex = 0;
            let record = await cursor.next();

            // Skip to offset
            while (record && currentIndex < offset) {
                record = await cursor.next();
                currentIndex++;
            }

            // Collect rows up to limit
            while (record && rows.length < limit && currentIndex < this.totalRows) {
                // Apply search filter if present
                if (searchTerm) {
                    const rowText = JSON.stringify(record).toLowerCase();
                    if (!rowText.includes(searchTerm)) {
                        record = await cursor.next();
                        currentIndex++;
                        continue;
                    }
                }

                rows.push({
                    index: currentIndex,
                    data: this.normalizeParquetRecord(record)
                });

                record = await cursor.next();
                currentIndex++;
            }

            return {
                rows,
                hasMore: currentIndex < this.totalRows,
                nextOffset: currentIndex
            };
        } finally {
            // Cursor automatically cleaned up by garbage collection
        }
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
     * Converts row to JSON string
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
     * Extract schema information from Parquet schema
     * Maps Parquet types to our DataType enum
     */
    private extractSchemaInfo(): SchemaInfo {
        if (!this.schema) {
            return { columns: [] };
        }

        const columns: ColumnInfo[] = [];
        const fieldList = this.schema.fieldList;

        for (const field of fieldList) {
            columns.push({
                name: field.name,
                type: this.parquetTypeToDataType(field),
                nullable: field.repetitionType === 'OPTIONAL'
            });
        }

        return { columns };
    }

    /**
     * Map Parquet data type to our DataType enum
     */
    private parquetTypeToDataType(field: any): DataType {
        const primitiveType = field.primitiveType;
        const originalType = field.originalType;

        // Check originalType first (more specific)
        if (originalType) {
            switch (originalType.toUpperCase()) {
                case 'UTF8':
                case 'JSON':
                case 'BSON':
                    return DataType.STRING;
                case 'INT_8':
                case 'INT_16':
                case 'INT_32':
                case 'INT_64':
                case 'UINT_8':
                case 'UINT_16':
                case 'UINT_32':
                case 'UINT_64':
                    return DataType.INTEGER;
                case 'DATE':
                case 'TIME_MILLIS':
                case 'TIME_MICROS':
                case 'TIMESTAMP_MILLIS':
                case 'TIMESTAMP_MICROS':
                    return DataType.DATETIME;
                case 'DECIMAL':
                    return DataType.FLOAT;
                case 'LIST':
                    return DataType.ARRAY;
                case 'MAP':
                    return DataType.OBJECT;
            }
        }

        // Fall back to primitiveType
        if (primitiveType) {
            switch (primitiveType.toUpperCase()) {
                case 'BOOLEAN':
                    return DataType.BOOLEAN;
                case 'INT32':
                case 'INT64':
                    return DataType.INTEGER;
                case 'INT96':
                    return DataType.DATETIME;
                case 'FLOAT':
                case 'DOUBLE':
                    return DataType.FLOAT;
                case 'BYTE_ARRAY':
                    // Could be string or binary
                    return originalType === 'UTF8' ? DataType.STRING : DataType.BINARY;
                case 'FIXED_LEN_BYTE_ARRAY':
                    return DataType.BINARY;
            }
        }

        // Check if it's a repeated field (array)
        if (field.repetitionType === 'REPEATED') {
            return DataType.ARRAY;
        }

        // Default to Object for complex types
        return DataType.OBJECT;
    }

    /**
     * Normalize Parquet nested structures to standard JSON format
     *
     * Parquetjs returns nested lists in this format:
     *   {messages: {list: [{element: {role: "user", content: "..."}}, ...]}}
     *
     * This normalizes it to:
     *   {messages: [{role: "user", content: "..."}, ...]}
     */
    private normalizeParquetRecord(record: any): any {
        if (record === null || record === undefined) {
            return record;
        }

        if (typeof record !== 'object') {
            return record;
        }

        if (Array.isArray(record)) {
            return record.map(item => this.normalizeParquetRecord(item));
        }

        // Check if this is a Parquet list structure: {list: [{element: ...}, ...]}
        if (record.list && Array.isArray(record.list)) {
            return record.list.map((item: any) => {
                if (item && item.element !== undefined) {
                    return this.normalizeParquetRecord(item.element);
                }
                return this.normalizeParquetRecord(item);
            });
        }

        // Recursively normalize all object properties
        const normalized: any = {};
        for (const key of Object.keys(record)) {
            normalized[key] = this.normalizeParquetRecord(record[key]);
        }
        return normalized;
    }

    /**
     * Clean up resources
     */
    async dispose(): Promise<void> {
        if (this.reader) {
            await this.reader.close();
            this.reader = undefined;
        }
        this.schema = undefined;
    }
}
