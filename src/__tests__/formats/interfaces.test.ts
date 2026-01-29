import { IDataLoader, FileMetadata, RowBatch, DataRow } from '../../formats/interfaces';
import { LoadLinesMessage, LinesResponseMessage } from '../../webview/types/messages';

describe('IDataLoader Interface', () => {
  test('interface can be implemented', () => {
    // Test that a mock implementation compiles
    class MockLoader implements IDataLoader {
      async initialize(filePath: string): Promise<void> {}
      async getMetadata(): Promise<FileMetadata> {
        return { format: 'jsonl', fileSizeBytes: 0 };
      }
      async loadRows(offset: number, limit: number): Promise<RowBatch> {
        return { rows: [], hasMore: false, nextOffset: 0 };
      }
      async jumpToRow(rowNumber: number): Promise<RowBatch> {
        return { rows: [], hasMore: false, nextOffset: 0 };
      }
      extractTextForTokens(row: any): string {
        return '';
      }
      dispose(): void {}
    }
    expect(new MockLoader()).toBeDefined();
  });

  test('mock loader returns expected metadata', async () => {
    class MockLoader implements IDataLoader {
      async initialize(filePath: string): Promise<void> {}
      async getMetadata(): Promise<FileMetadata> {
        return {
          format: 'jsonl',
          fileSizeBytes: 12345,
          totalRows: 100
        };
      }
      async loadRows(offset: number, limit: number): Promise<RowBatch> {
        return { rows: [], hasMore: false, nextOffset: 0 };
      }
      async jumpToRow(rowNumber: number): Promise<RowBatch> {
        return { rows: [], hasMore: false, nextOffset: 0 };
      }
      extractTextForTokens(row: any): string {
        return JSON.stringify(row);
      }
      dispose(): void {}
    }

    const loader = new MockLoader();
    await loader.initialize('/test/file.jsonl');
    const metadata = await loader.getMetadata();

    expect(metadata.format).toBe('jsonl');
    expect(metadata.fileSizeBytes).toBe(12345);
    expect(metadata.totalRows).toBe(100);
  });

  test('mock loader returns row batch', async () => {
    const testRow: DataRow = {
      index: 0,
      data: { test: 'data' },
      raw: '{"test":"data"}',
      tokens: 5
    };

    class MockLoader implements IDataLoader {
      async initialize(filePath: string): Promise<void> {}
      async getMetadata(): Promise<FileMetadata> {
        return { format: 'jsonl', fileSizeBytes: 100 };
      }
      async loadRows(offset: number, limit: number): Promise<RowBatch> {
        return {
          rows: [testRow],
          hasMore: false,
          nextOffset: 1
        };
      }
      async jumpToRow(rowNumber: number): Promise<RowBatch> {
        return this.loadRows(rowNumber, 100);
      }
      extractTextForTokens(row: any): string {
        return JSON.stringify(row);
      }
      dispose(): void {}
    }

    const loader = new MockLoader();
    await loader.initialize('/test/file.jsonl');
    const batch = await loader.loadRows(0, 100);

    expect(batch.rows).toHaveLength(1);
    expect(batch.rows[0].index).toBe(0);
    expect(batch.rows[0].data).toEqual({ test: 'data' });
    expect(batch.hasMore).toBe(false);
    expect(batch.nextOffset).toBe(1);
  });
});

describe('Message Types', () => {
  test('LoadLinesMessage type is correctly defined', () => {
    const msg: LoadLinesMessage = {
      type: 'loadLines',
      offset: 0,
      limit: 100,
      tokenizer: 'gpt-4'
    };
    expect(msg.type).toBe('loadLines');
    expect(msg.offset).toBe(0);
    expect(msg.limit).toBe(100);
    expect(msg.tokenizer).toBe('gpt-4');
  });

  test('LoadLinesMessage with search term', () => {
    const msg: LoadLinesMessage = {
      type: 'loadLines',
      offset: 0,
      limit: 100,
      searchTerm: 'test',
      tokenizer: 'gpt-4'
    };
    expect(msg.searchTerm).toBe('test');
  });

  test('LinesResponseMessage type is correctly defined', () => {
    const testRow: DataRow = {
      index: 0,
      data: { test: 'data' },
      raw: '{"test":"data"}'
    };

    const msg: LinesResponseMessage = {
      type: 'lines',
      lines: [testRow],
      hasMore: true,
      nextOffset: 100
    };

    expect(msg.type).toBe('lines');
    expect(msg.lines).toHaveLength(1);
    expect(msg.hasMore).toBe(true);
    expect(msg.nextOffset).toBe(100);
  });
});
