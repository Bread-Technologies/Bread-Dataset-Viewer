import * as vscode from 'vscode';
import { BaseDataProvider } from './BaseDataProvider';
import { IDataLoader } from '../formats/interfaces';
import { CsvDataLoader } from '../formats/loaders/CsvDataLoader';

/**
 * Provider for CSV and TSV files
 *
 * Supports both comma-separated and tab-separated values with automatic delimiter detection.
 */
export class CsvDataProvider extends BaseDataProvider {
    constructor(context: vscode.ExtensionContext) {
        super(context, ['csv', 'tsv']);
    }

    /**
     * Create a CsvDataLoader for the given file path
     */
    createLoader(filePath: string): IDataLoader {
        return new CsvDataLoader();
    }
}
