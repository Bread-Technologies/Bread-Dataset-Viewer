import { JsonlDataProvider } from '../../providers/JsonlDataProvider';
import { JsonlDataLoader } from '../../formats/loaders/JsonlDataLoader';

describe('JsonlDataProvider', () => {
  let provider: JsonlDataProvider;
  let mockContext: any;

  beforeEach(() => {
    mockContext = { extensionPath: '/test/path' };
    provider = new JsonlDataProvider(mockContext);
  });

  test('creates JsonlDataLoader', () => {
    const loader = provider.createLoader('/test/file.jsonl');
    expect(loader).toBeInstanceOf(JsonlDataLoader);
  });

  test('supports jsonl format', () => {
    expect(provider['supportedFormats']).toContain('jsonl');
  });

  test('can be instantiated', () => {
    expect(provider).toBeDefined();
    expect(provider).toBeInstanceOf(JsonlDataProvider);
  });
});
