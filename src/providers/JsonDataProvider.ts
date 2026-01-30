import * as vscode from 'vscode';
import { BaseDataProvider } from './BaseDataProvider';
import { IDataLoader } from '../formats/interfaces';
import { JsonDataLoader } from '../formats/loaders/JsonDataLoader';

/**
 * Custom editor provider for standard JSON files
 * Extends BaseDataProvider to provide format-specific loader
 */
export class JsonDataProvider extends BaseDataProvider {
    constructor(context: vscode.ExtensionContext) {
        super(context, ['json']);
    }

    /**
     * Create a JSON data loader
     */
    createLoader(filePath: string): IDataLoader {
        return new JsonDataLoader();
    }
}
