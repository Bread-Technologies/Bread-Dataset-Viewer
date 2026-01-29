import * as vscode from 'vscode';
import { BaseDataProvider } from './BaseDataProvider';
import { IDataLoader } from '../formats/interfaces';
import { ArrowDataLoader } from '../formats/loaders/ArrowDataLoader';

/**
 * Provider for Apache Arrow IPC files (.arrow, .feather)
 *
 * Arrow format is ideal for ML workflows:
 * - Used by Hugging Face datasets
 * - Pandas to_feather() export
 * - Columnar format optimized for analytics
 * - Full schema with type information
 */
export class ArrowDataProvider extends BaseDataProvider {
    constructor(context: vscode.ExtensionContext) {
        super(context, ['arrow', 'feather']);
    }

    createLoader(filePath: string): IDataLoader {
        return new ArrowDataLoader();
    }
}
