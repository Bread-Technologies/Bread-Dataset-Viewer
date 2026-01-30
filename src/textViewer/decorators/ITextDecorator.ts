import * as vscode from 'vscode';

/**
 * Interface for format-specific syntax highlighting decorators
 */
export interface ITextDecorator {
    /**
     * Analyzes document and returns ranges to highlight
     * @param document - The text document to analyze
     * @returns Map of decoration type → ranges to apply
     */
    getDecorationRanges(document: vscode.TextDocument): Map<string, vscode.Range[]>;

    /**
     * Creates VS Code decoration types with colors
     * @returns Map of decoration name → decoration type
     */
    createDecorationTypes(): Map<string, vscode.TextEditorDecorationType>;
}
