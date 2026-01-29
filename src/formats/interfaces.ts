/**
 * Core abstractions for multi-format data loading
 */

/**
 * Supported file formats
 */
export type FileFormat = 'jsonl' | 'parquet' | 'csv' | 'tsv';

/**
 * Data type enum for schema columns
 */
export enum DataType {
    STRING = 'string',
    NUMBER = 'number',
    BOOLEAN = 'boolean',
    OBJECT = 'object',
    ARRAY = 'array',
    NULL = 'null',
    INT32 = 'int32',
    INT64 = 'int64',
    FLOAT = 'float',
    DOUBLE = 'double',
    DATE = 'date',
    TIMESTAMP = 'timestamp'
}

/**
 * Column information for schema
 */
export interface ColumnInfo {
    name: string;
    type: DataType;
    nullable?: boolean;
}

/**
 * Schema information for structured data
 */
export interface SchemaInfo {
    columns: ColumnInfo[];
}

/**
 * Metadata about a data file
 */
export interface FileMetadata {
    format: FileFormat;
    fileSizeBytes: number;
    totalRows?: number;        // Optional: some formats can't know without scanning
    schema?: SchemaInfo;       // Column names and types
    compressionType?: string;  // For Parquet
}

/**
 * A single data row
 */
export interface DataRow {
    index: number;             // Zero-based line/row number
    data: any;                 // Parsed data object
    raw?: string;              // Raw string representation (for JSONL, CSV)
    error?: string;            // Error message if parsing failed
    tokens?: number;           // Token count for this row
}

/**
 * Batch of rows returned by loader
 */
export interface RowBatch {
    rows: DataRow[];
    hasMore: boolean;
    nextOffset: number;
}

/**
 * Filter options for loading rows
 */
export interface FilterOptions {
    searchTerm?: string;
    selectedPaths?: Set<string>;
}

/**
 * Interface that all format loaders must implement
 *
 * Key Requirements:
 * - Streaming-first: Never load entire file into memory
 * - Pagination: Load rows in batches (typically 100 at a time)
 * - Filtering: Support search terms without full file scan
 * - Format-agnostic: Same interface for all formats
 */
export interface IDataLoader {
    /**
     * Initialize the loader with a file path
     * @param filePath Absolute path to the data file
     */
    initialize(filePath: string): Promise<void>;

    /**
     * Get metadata about the file
     * @returns File metadata including format, size, schema, etc.
     */
    getMetadata(): Promise<FileMetadata>;

    /**
     * Load a batch of rows from the file
     * @param offset Starting row/line number (zero-based)
     * @param limit Maximum number of rows to load
     * @param filter Optional filter options (search term, selected paths)
     * @returns Batch of rows with pagination info
     */
    loadRows(offset: number, limit: number, filter?: FilterOptions): Promise<RowBatch>;

    /**
     * Jump to a specific row and load a batch from that point
     * @param rowNumber Row number to jump to (zero-based)
     * @returns Batch of rows starting from the specified row
     */
    jumpToRow(rowNumber: number): Promise<RowBatch>;

    /**
     * Extract text from a row for token counting
     * @param row Row data object
     * @returns String representation for token counting
     */
    extractTextForTokens(row: any): string;

    /**
     * Clean up resources (close streams, etc.)
     */
    dispose(): void;
}
