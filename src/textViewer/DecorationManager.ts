import * as vscode from 'vscode';
import { ITextDecorator } from './decorators/ITextDecorator';

/**
 * Manages format-specific decorations for text viewers
 * Registers decorators per format and applies them to editors
 */
export class DecorationManager {
    private decorators = new Map<string, ITextDecorator>();
    private decorationTypes = new Map<string, Map<string, vscode.TextEditorDecorationType>>();

    constructor(private context: vscode.ExtensionContext) {}

    /**
     * Register a decorator for a specific format
     * @param format - File format (jsonl, csv, etc.)
     * @param decorator - Decorator implementation
     */
    registerDecorator(format: string, decorator: ITextDecorator): void {
        this.decorators.set(format, decorator);

        // Create and cache decoration types
        const types = decorator.createDecorationTypes();
        this.decorationTypes.set(format, types);

        // Register for disposal
        types.forEach(type => this.context.subscriptions.push(type));
    }

    /**
     * Apply decorations to an editor based on format
     * @param editor - The text editor to decorate
     * @param format - The file format
     */
    applyDecorations(editor: vscode.TextEditor, format: string): void {
        const decorator = this.decorators.get(format);
        const decorationTypes = this.decorationTypes.get(format);

        if (!decorator || !decorationTypes) {
            // No decorator registered for this format
            return;
        }

        const ranges = decorator.getDecorationRanges(editor.document);

        ranges.forEach((rangeList, tokenType) => {
            const decorationType = decorationTypes.get(tokenType);
            if (decorationType) {
                editor.setDecorations(decorationType, rangeList);
            }
        });
    }

    /**
     * Clear all decorations from an editor
     * @param editor - The text editor to clear
     */
    clearDecorations(editor: vscode.TextEditor): void {
        this.decorationTypes.forEach((types) => {
            types.forEach((decorationType) => {
                editor.setDecorations(decorationType, []);
            });
        });
    }
}
