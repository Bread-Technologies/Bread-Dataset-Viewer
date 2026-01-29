import { ArrowDataProvider } from '../../providers/ArrowDataProvider';
import { ArrowDataLoader } from '../../formats/loaders/ArrowDataLoader';

describe('ArrowDataProvider', () => {
  let provider: ArrowDataProvider;
  let mockContext: any;

  beforeEach(() => {
    mockContext = { extensionPath: '/test/path' };
    provider = new ArrowDataProvider(mockContext);
  });

  test('creates ArrowDataLoader for Arrow files', () => {
    const loader = provider.createLoader('/test/file.arrow');
    expect(loader).toBeInstanceOf(ArrowDataLoader);
  });

  test('creates ArrowDataLoader for Feather files', () => {
    const loader = provider.createLoader('/test/file.feather');
    expect(loader).toBeInstanceOf(ArrowDataLoader);
  });

  test('supports arrow format', () => {
    expect(provider['supportedFormats']).toContain('arrow');
  });

  test('supports feather format', () => {
    expect(provider['supportedFormats']).toContain('feather');
  });

  test('can be instantiated', () => {
    expect(provider).toBeDefined();
    expect(provider).toBeInstanceOf(ArrowDataProvider);
  });

  test('extends BaseDataProvider', () => {
    // Check that provider has methods from BaseDataProvider
    expect(typeof provider.createLoader).toBe('function');
    expect(typeof provider['supportedFormats']).toBe('object');
  });
});
