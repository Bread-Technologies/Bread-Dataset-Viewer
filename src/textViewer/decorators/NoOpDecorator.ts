import * as vscode from 'vscode';
import { ITextDecorator } from './ITextDecorator';

/**
 * No-op decorator for formats that don't need syntax highlighting
 * Used for Parquet, Arrow, and other formats where highlighting isn't needed
 */
export class NoOpDecorator implements ITextDecorator {
    getDecorationRanges(_document: vscode.TextDocument): Map<string, vscode.Range[]> {
        return new Map();
    }

    createDecorationTypes(): Map<string, vscode.TextEditorDecorationType> {
        return new Map();
    }
}
