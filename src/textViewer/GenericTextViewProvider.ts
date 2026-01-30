import * as vscode from 'vscode';
import { BaseTextViewProvider } from './BaseTextViewProvider';
import { IDataLoader } from '../formats/interfaces';
import { JsonlDataLoader } from '../formats/loaders/JsonlDataLoader';
import { JsonDataLoader } from '../formats/loaders/JsonDataLoader';
import { CsvDataLoader } from '../formats/loaders/CsvDataLoader';
import { ParquetDataLoader } from '../formats/loaders/ParquetDataLoader';
import { ArrowDataLoader } from '../formats/loaders/ArrowDataLoader';
import { JsonRenderer } from './renderers/JsonRenderer';
import { CsvRenderer } from './renderers/CsvRenderer';
import { ParquetRenderer } from './renderers/ParquetRenderer';
import { ITextRenderer } from './renderers/ITextRenderer';

/**
 * Generic text view provider that supports multiple file formats
 * Uses format detection to create appropriate loaders and renderers
 */
export class GenericTextViewProvider extends BaseTextViewProvider {
    public static readonly scheme = 'data-text-view';

    constructor(context: vscode.ExtensionContext) {
        super(context, GenericTextViewProvider.scheme);
    }

    /**
     * Create format-specific data loader based on file extension
     */
    createLoader(fileUri: vscode.Uri): IDataLoader {
        const ext = fileUri.fsPath.split('.').pop()?.toLowerCase();

        switch (ext) {
            case 'jsonl': return new JsonlDataLoader();
            case 'json': return new JsonDataLoader();
            case 'csv':
            case 'tsv': return new CsvDataLoader();
            case 'parquet': return new ParquetDataLoader();
            case 'arrow':
            case 'feather': return new ArrowDataLoader();
            default:
                // Default to JSONL for unknown formats
                console.warn(`Unknown format: ${ext}, defaulting to JSONL`);
                return new JsonlDataLoader();
        }
    }

    /**
     * Create format-specific renderer based on format type
     */
    createRenderer(format: string): ITextRenderer {
        switch (format) {
            case 'jsonl':
            case 'json':
                return new JsonRenderer();

            case 'csv':
            case 'tsv':
                return new CsvRenderer();

            case 'parquet':
            case 'arrow':
            case 'feather':
                return new ParquetRenderer();

            default:
                // Default to JSON renderer
                return new JsonRenderer();
        }
    }

    /**
     * Create a view URI for a given file URI
     * @param fileUri - The file to view
     * @param format - Optional explicit format (otherwise detected from extension)
     */
    static toViewUri(fileUri: vscode.Uri, format?: string): vscode.Uri {
        const encoded = encodeURIComponent(fileUri.toString());
        const formatParam = format ? `?format=${format}` : '';
        return vscode.Uri.parse(`${GenericTextViewProvider.scheme}:/${encoded}${formatParam}`);
    }

    /**
     * Get the underlying file URI from a view URI
     */
    static getFileUri(uri: vscode.Uri): vscode.Uri | undefined {
        if (uri.scheme === GenericTextViewProvider.scheme) {
            const encoded = uri.path.replace(/^\//, '');
            const decoded = decodeURIComponent(encoded);
            return vscode.Uri.parse(decoded);
        }
        if (uri.scheme === 'file') {
            return uri;
        }
        return undefined;
    }
}
