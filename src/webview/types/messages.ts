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
}

/**
 * Message from webview to extension: Jump to specific line
 */
export interface JumpToLineMessage extends BaseMessage {
    type: 'jumpToLine';
    lineNumber: number;
    tokenizer: string;
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
 * Message from extension to webview: Token counts
 */
export interface TokensMessage extends BaseMessage {
    type: 'tokens';
    counts: { [index: number]: number };
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
