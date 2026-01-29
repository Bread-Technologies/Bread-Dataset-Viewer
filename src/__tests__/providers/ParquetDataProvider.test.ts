import { ParquetDataProvider } from '../../providers/ParquetDataProvider';
import { ParquetDataLoader } from '../../formats/loaders/ParquetDataLoader';

describe('ParquetDataProvider', () => {
  let provider: ParquetDataProvider;
  let mockContext: any;

  beforeEach(() => {
    mockContext = { extensionPath: '/test/path' };
    provider = new ParquetDataProvider(mockContext);
  });

  test('creates ParquetDataLoader', () => {
    const loader = provider.createLoader('/test/file.parquet');
    expect(loader).toBeInstanceOf(ParquetDataLoader);
  });

  test('supports parquet format', () => {
    expect(provider['supportedFormats']).toContain('parquet');
  });

  test('can be instantiated', () => {
    expect(provider).toBeDefined();
    expect(provider).toBeInstanceOf(ParquetDataProvider);
  });
});
