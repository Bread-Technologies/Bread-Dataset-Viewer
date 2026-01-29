import * as vscode from 'vscode';
import { BaseDataProvider } from './BaseDataProvider';
import { IDataLoader } from '../formats/interfaces';
import { JsonlDataLoader } from '../formats/loaders/JsonlDataLoader';

/**
 * Custom editor provider for JSONL (JSON Lines) files
 * Extends BaseDataProvider to provide format-specific loader
 */
export class JsonlDataProvider extends BaseDataProvider {
    constructor(context: vscode.ExtensionContext) {
        super(context, ['jsonl']);
    }

    /**
     * Create a JSONL data loader
     */
    createLoader(filePath: string): IDataLoader {
        return new JsonlDataLoader();
    }
}
