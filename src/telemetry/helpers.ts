/**
 * Helper utilities for telemetry tracking
 */

/**
 * Categorize file size into buckets for telemetry
 * @param bytes File size in bytes
 * @returns Size category string
 */
export function getFileSizeCategory(bytes: number): string {
    if (bytes < 1024 * 1024) return 'small'; // < 1MB
    if (bytes < 10 * 1024 * 1024) return 'medium'; // 1-10MB
    if (bytes < 100 * 1024 * 1024) return 'large'; // 10-100MB
    if (bytes < 1024 * 1024 * 1024) return 'xlarge'; // 100MB-1GB
    return 'huge'; // > 1GB
}

/**
 * Categorize row count into buckets for telemetry
 * @param count Number of rows
 * @returns Count category string
 */
export function getRowCountCategory(count: number): string {
    if (count < 100) return 'tiny';
    if (count < 1000) return 'small';
    if (count < 10000) return 'medium';
    if (count < 100000) return 'large';
    return 'huge';
}

/**
 * Sanitize user input for telemetry (search terms, etc.)
 * Never sends actual input, only categorizes by length
 * @param input User input string
 * @returns Length category string
 */
export function sanitizeUserInput(input: string): string {
    if (!input || input.length === 0) return 'empty';
    if (input.length < 5) return 'short';
    if (input.length < 20) return 'medium';
    return 'long';
}

/**
 * Get format from file extension
 * @param filePath File path or name
 * @returns Format string
 */
export function getFormatFromPath(filePath: string): string {
    const ext = filePath.split('.').pop()?.toLowerCase();
    return ext || 'unknown';
}

/**
 * Categorize duration for telemetry
 * @param durationMs Duration in milliseconds
 * @returns Duration category
 */
export function getDurationCategory(durationMs: number): string {
    if (durationMs < 100) return 'fast'; // < 100ms
    if (durationMs < 1000) return 'moderate'; // 100ms-1s
    if (durationMs < 5000) return 'slow'; // 1-5s
    return 'very-slow'; // > 5s
}
