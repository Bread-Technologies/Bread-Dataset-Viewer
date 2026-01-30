import { BaseDataProvider } from '../../providers/BaseDataProvider';
import { IDataLoader, FileMetadata, RowBatch, FileFormat } from '../../formats/interfaces';

class MockLoader implements IDataLoader {
  async initialize(filePath: string): Promise<void> {}
  async getMetadata(): Promise<FileMetadata> {
    return { format: 'jsonl', fileSizeBytes: 100 };
  }
  async loadRows(offset: number, limit: number): Promise<RowBatch> {
    return {
      rows: [{ index: offset, data: { test: 'data' }, raw: '{"test":"data"}' }],
      hasMore: false,
      nextOffset: offset + 1
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

class TestProvider extends BaseDataProvider {
  createLoader(filePath: string): IDataLoader {
    return new MockLoader();
  }
}

describe('BaseDataProvider', () => {
  let provider: TestProvider;
  let mockContext: any;

  beforeEach(() => {
    mockContext = { extensionPath: '/test/path' };
    provider = new TestProvider(mockContext, ['jsonl']);
  });

  test('creates loader correctly', () => {
    const loader = provider.createLoader('/test/file.jsonl');
    expect(loader).toBeInstanceOf(MockLoader);
  });

  test('supports specified formats', () => {
    expect(provider['supportedFormats']).toContain('jsonl');
  });

  test('can be instantiated', () => {
    expect(provider).toBeDefined();
    expect(provider).toBeInstanceOf(BaseDataProvider);
    expect(provider).toBeInstanceOf(TestProvider);
  });

  test('has required methods', () => {
    expect(typeof provider.openCustomDocument).toBe('function');
    expect(typeof provider.resolveCustomEditor).toBe('function');
    expect(typeof provider.createLoader).toBe('function');
  });
});
