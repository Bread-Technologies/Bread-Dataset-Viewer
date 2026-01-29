import { CsvDataProvider } from '../../providers/CsvDataProvider';
import { CsvDataLoader } from '../../formats/loaders/CsvDataLoader';

describe('CsvDataProvider', () => {
  let provider: CsvDataProvider;
  let mockContext: any;

  beforeEach(() => {
    mockContext = { extensionPath: '/test/path' };
    provider = new CsvDataProvider(mockContext);
  });

  test('creates CsvDataLoader', () => {
    const loader = provider.createLoader('/test/file.csv');
    expect(loader).toBeInstanceOf(CsvDataLoader);
  });

  test('supports csv format', () => {
    expect(provider['supportedFormats']).toContain('csv');
  });

  test('supports tsv format', () => {
    expect(provider['supportedFormats']).toContain('tsv');
  });

  test('can be instantiated', () => {
    expect(provider).toBeDefined();
    expect(provider).toBeInstanceOf(CsvDataProvider);
  });
});
