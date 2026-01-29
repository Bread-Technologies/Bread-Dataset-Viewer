/**
 * TypeScript interfaces for extension ↔ webview message protocol
 */

import { DataRow } from '../../formats/interfaces';

/**
 * Base message interface
 */
interface BaseMessage {
    type: string;
}

/**
 * Message from webview to extension: Load lines/rows
 */
export interface LoadLinesMessage extends BaseMessage {
    type: 'loadLines';
    offset: number;
    limit: number;
    searchTerm?: string;
    tokenizer: string;
    tokenMode?: string;
}

/**
 * Message from webview to extension: Jump to specific line
 */
export interface JumpToLineMessage extends BaseMessage {
    type: 'jumpToLine';
    lineNumber: number;
    tokenizer: string;
    tokenMode?: string;
}

/**
 * Message from webview to extension: Open in text editor
 */
export interface OpenInTextEditorMessage extends BaseMessage {
    type: 'openInTextEditor';
}

/**
 * Message from extension to webview: Lines/rows response
 */
export interface LinesResponseMessage extends BaseMessage {
    type: 'lines';
    lines: DataRow[];
    hasMore: boolean;
    nextOffset: number;
}

/**
 * Token count result for a single row
 */
export interface TokenCountData {
    count: number;
    mode: 'chat' | 'full-json' | 'key' | 'raw-text' | 'error';
    key?: string;
    preview?: string;
    error?: string;
}

/**
 * Message from extension to webview: Token counts
 */
export interface TokensMessage extends BaseMessage {
    type: 'tokens';
    tokens: { [index: number]: TokenCountData };
}

/**
 * Message from extension to webview: Token errors
 */
export interface TokenErrorsMessage extends BaseMessage {
    type: 'tokenErrors';
    errors: string[];
}

/**
 * Message from extension to webview: File information
 */
export interface FileInfoMessage extends BaseMessage {
    type: 'fileInfo';
    fileName: string;
    fileSize: string;
    format?: string;
    schema?: any;
}

/**
 * Union type of all messages from webview to extension
 */
export type WebviewToExtensionMessage =
    | LoadLinesMessage
    | JumpToLineMessage
    | OpenInTextEditorMessage;

/**
 * Union type of all messages from extension to webview
 */
export type ExtensionToWebviewMessage =
    | LinesResponseMessage
    | TokensMessage
    | FileInfoMessage;
