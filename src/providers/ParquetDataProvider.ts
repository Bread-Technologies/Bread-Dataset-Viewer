import * as vscode from 'vscode';
import { BaseDataProvider } from './BaseDataProvider';
import { IDataLoader } from '../formats/interfaces';
import { ParquetDataLoader } from '../formats/loaders/ParquetDataLoader';

/**
 * Custom editor provider for Parquet files
 * Extends BaseDataProvider to provide format-specific loader
 */
export class ParquetDataProvider extends BaseDataProvider {
    constructor(context: vscode.ExtensionContext) {
        super(context, ['parquet']);
    }

    /**
     * Create a Parquet data loader
     */
    createLoader(filePath: string): IDataLoader {
        return new ParquetDataLoader();
    }
}
