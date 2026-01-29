import * as path from 'path';
import { JsonlDataLoader } from '../../formats/loaders/JsonlDataLoader';

describe('JsonlDataLoader', () => {
  let testFilePath: string;
  let loader: JsonlDataLoader;

  beforeEach(() => {
    loader = new JsonlDataLoader();
    // Path to test.jsonl from project root
    testFilePath = path.join(process.cwd(), 'test-data', 'test.jsonl');
  });

  afterEach(() => {
    loader.dispose();
  });

  describe('initialize', () => {
    test('initializes with valid file', async () => {
      await loader.initialize(testFilePath);
      const metadata = await loader.getMetadata();
      expect(metadata.format).toBe('jsonl');
      expect(metadata.fileSizeBytes).toBeGreaterThan(0);
    });

    test('throws error for non-existent file', async () => {
      await expect(loader.initialize('/nonexistent.jsonl')).rejects.toThrow();
    });
  });

  describe('loadRows', () => {
    beforeEach(async () => {
      await loader.initialize(testFilePath);
    });

    test('loads first 100 rows', async () => {
      const result = await loader.loadRows(0, 100);
      expect(result.rows.length).toBeLessThanOrEqual(100);
      expect(result.rows[0].index).toBe(0);
      expect(result.hasMore).toBe(true);
      expect(result.nextOffset).toBe(100);
    });

    test('handles pagination correctly', async () => {
      const batch1 = await loader.loadRows(0, 10);
      const batch2 = await loader.loadRows(10, 10);
      expect(batch2.rows[0].index).toBe(10);
      expect(batch2.rows).toHaveLength(10);
    });

    test('handles malformed JSON gracefully', async () => {
      // test.jsonl has malformed JSON at line 99 (every 100th line)
      const result = await loader.loadRows(0, 100);
      const errorRows = result.rows.filter(r => r.error);
      expect(errorRows.length).toBeGreaterThanOrEqual(1);
      expect(errorRows[0].error).toBe('Invalid JSON');
      expect(errorRows[0].data).toBeNull();
    });

    test('supports search filtering', async () => {
      const result = await loader.loadRows(0, 100, { searchTerm: 'line 5' });
      // Should find rows with "line 5", "line 50", "line 51", etc.
      expect(result.rows.length).toBeGreaterThan(0);
      result.rows.forEach(row => {
        if (!row.error) {
          expect(row.raw?.toLowerCase()).toContain('line 5');
        }
      });
    });

    test('handles offset beyond file end', async () => {
      const result = await loader.loadRows(1000000, 100);
      expect(result.rows).toHaveLength(0);
      expect(result.hasMore).toBe(false);
    });

    test('returns correct nextOffset', async () => {
      const result = await loader.loadRows(0, 50);
      expect(result.nextOffset).toBe(50);
    });

    test('hasMore is false when reaching end of file', async () => {
      // test.jsonl has 1000 lines
      const result = await loader.loadRows(950, 100);
      expect(result.hasMore).toBe(false);
    });
  });

  describe('jumpToRow', () => {
    beforeEach(async () => {
      await loader.initialize(testFilePath);
    });

    test('jumps to specific row', async () => {
      const result = await loader.jumpToRow(500);
      expect(result.rows[0].index).toBe(500);
      expect(result.rows.length).toBeLessThanOrEqual(100);
    });

    test('jumps to row near end of file', async () => {
      const result = await loader.jumpToRow(950);
      expect(result.rows[0].index).toBe(950);
      expect(result.hasMore).toBe(false);
    });
  });

  describe('extractTextForTokens', () => {
    test('converts row data to JSON string', () => {
      const row = { test: 'data', nested: { value: 123 } };
      const text = loader.extractTextForTokens(row);
      expect(text).toBe(JSON.stringify(row));
    });

    test('handles string input', () => {
      const text = loader.extractTextForTokens('{"test":"data"}');
      expect(text).toBe('{"test":"data"}');
    });
  });

  describe('memory efficiency', () => {
    test('does not load entire file into memory', async () => {
      // Use large.jsonl (4.2MB, 100k lines)
      const largePath = path.join(process.cwd(), 'test-data', 'large.jsonl');
      await loader.initialize(largePath);

      const memBefore = process.memoryUsage().heapUsed;
      await loader.loadRows(0, 100);
      const memAfter = process.memoryUsage().heapUsed;

      // Memory increase should be minimal (< 10MB), much less than file size
      const memDelta = (memAfter - memBefore) / 1024 / 1024; // MB
      expect(memDelta).toBeLessThan(10);
    });

    test('handles multiple sequential loads without memory accumulation', async () => {
      await loader.initialize(testFilePath);

      const memBefore = process.memoryUsage().heapUsed;

      // Load 10 batches sequentially
      for (let i = 0; i < 10; i++) {
        await loader.loadRows(i * 100, 100);
      }

      const memAfter = process.memoryUsage().heapUsed;
      const memDelta = (memAfter - memBefore) / 1024 / 1024; // MB

      // Memory should not accumulate significantly
      expect(memDelta).toBeLessThan(5);
    });
  });

  describe('data integrity', () => {
    beforeEach(async () => {
      await loader.initialize(testFilePath);
    });

    test('preserves zero-based indexing', async () => {
      const result = await loader.loadRows(0, 10);
      expect(result.rows[0].index).toBe(0);
      expect(result.rows[9].index).toBe(9);
    });

    test('correctly parses JSON data', async () => {
      const result = await loader.loadRows(0, 1);
      const row = result.rows[0];
      expect(row.data).toBeDefined();
      expect(row.data.id).toBe(0);
      expect(row.data.text).toBe('Test line 0');
    });

    test('includes raw line in result', async () => {
      const result = await loader.loadRows(0, 1);
      const row = result.rows[0];
      expect(row.raw).toBeDefined();
      expect(row.raw).toContain('"id":0');
    });
  });
});
