import * as path from 'path';
import { ParquetDataLoader } from '../../formats/loaders/ParquetDataLoader';
import { DataType } from '../../formats/interfaces';

describe('ParquetDataLoader', () => {
  let testFilePath: string;
  let loader: ParquetDataLoader;

  beforeEach(() => {
    loader = new ParquetDataLoader();
    // Path to test.parquet from project root
    testFilePath = path.join(process.cwd(), 'test-data', 'test.parquet');
  });

  afterEach(async () => {
    await loader.dispose();
  });

  describe('initialize', () => {
    test('initializes with valid parquet file', async () => {
      await loader.initialize(testFilePath);
      const metadata = await loader.getMetadata();
      expect(metadata.format).toBe('parquet');
      expect(metadata.fileSizeBytes).toBeGreaterThan(0);
      expect(metadata.totalRows).toBe(1000);
    });

    test('throws error for non-existent file', async () => {
      await expect(loader.initialize('/nonexistent.parquet')).rejects.toThrow();
    });

    test('extracts schema correctly', async () => {
      await loader.initialize(testFilePath);
      const metadata = await loader.getMetadata();

      expect(metadata.schema).toBeDefined();
      expect(metadata.schema?.columns).toBeDefined();

      if (!metadata.schema) {
        throw new Error('Schema is undefined');
      }

      expect(metadata.schema.columns.length).toBeGreaterThan(0);

      // Check for expected columns
      const columnNames = metadata.schema.columns.map(c => c.name);
      expect(columnNames).toContain('id');
      expect(columnNames).toContain('name');
      expect(columnNames).toContain('value');
      expect(columnNames).toContain('active');
    });

    test('maps data types correctly', async () => {
      await loader.initialize(testFilePath);
      const metadata = await loader.getMetadata();

      const idCol = metadata.schema?.columns.find(c => c.name === 'id');
      const nameCol = metadata.schema?.columns.find(c => c.name === 'name');
      const valueCol = metadata.schema?.columns.find(c => c.name === 'value');
      const activeCol = metadata.schema?.columns.find(c => c.name === 'active');

      expect(idCol?.type).toBe(DataType.INTEGER);
      expect(nameCol?.type).toBe(DataType.STRING);
      expect(valueCol?.type).toBe(DataType.FLOAT);
      expect(activeCol?.type).toBe(DataType.BOOLEAN);
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

    test('handles pagination efficiently', async () => {
      const batch1 = await loader.loadRows(0, 50);
      const batch2 = await loader.loadRows(50, 50);

      expect(batch1.rows.length).toBe(50);
      expect(batch2.rows.length).toBe(50);
      expect(batch2.rows[0].index).toBe(50);
    });

    test('parses row data correctly', async () => {
      const result = await loader.loadRows(0, 1);
      const row = result.rows[0];

      expect(row.data).toBeDefined();
      expect(row.data.id).toBe(0);
      expect(row.data.name).toBe('User 0');
      expect(row.data.value).toBe(0);
      expect(row.data.active).toBe(true);
    });

    test('handles array columns', async () => {
      const result = await loader.loadRows(0, 10);

      result.rows.forEach(row => {
        expect(Array.isArray(row.data.tags)).toBe(true);
        expect(row.data.tags.length).toBeGreaterThan(0);
      });
    });

    test('supports search filtering', async () => {
      const result = await loader.loadRows(0, 100, { searchTerm: 'User 5' });

      // Should find rows with "User 5", "User 50", "User 51", etc.
      expect(result.rows.length).toBeGreaterThan(0);
      result.rows.forEach(row => {
        const text = JSON.stringify(row.data).toLowerCase();
        expect(text).toContain('user 5');
      });
    });

    test('handles offset beyond file end', async () => {
      const result = await loader.loadRows(2000, 100);
      expect(result.rows).toHaveLength(0);
      expect(result.hasMore).toBe(false);
    });

    test('returns correct nextOffset', async () => {
      const result = await loader.loadRows(0, 50);
      expect(result.nextOffset).toBe(50);
    });

    test('hasMore is false when reaching end of file', async () => {
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
      const row = { id: 1, name: 'Test', value: 123.45 };
      const text = loader.extractTextForTokens(row);
      expect(text).toBe(JSON.stringify(row));
    });

    test('handles string input', () => {
      const text = loader.extractTextForTokens('{"id":1}');
      expect(text).toBe('{"id":1}');
    });
  });

  describe('memory efficiency', () => {
    test('does not load entire file into memory', async () => {
      // Use large.parquet (100k rows)
      const largePath = path.join(process.cwd(), 'test-data', 'large.parquet');
      await loader.initialize(largePath);

      const memBefore = process.memoryUsage().heapUsed;
      await loader.loadRows(0, 100);
      const memAfter = process.memoryUsage().heapUsed;

      // Memory increase should be minimal (< 50MB), much less than file size
      const memDelta = (memAfter - memBefore) / 1024 / 1024; // MB
      expect(memDelta).toBeLessThan(50);
    });

    test('handles multiple sequential loads without accumulation', async () => {
      await loader.initialize(testFilePath);

      const memBefore = process.memoryUsage().heapUsed;

      // Load 10 batches sequentially
      for (let i = 0; i < 10; i++) {
        await loader.loadRows(i * 100, 100);
      }

      const memAfter = process.memoryUsage().heapUsed;
      const memDelta = (memAfter - memBefore) / 1024 / 1024; // MB

      // Memory should not accumulate significantly
      expect(memDelta).toBeLessThan(20);
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

    test('correctly parses all data types', async () => {
      const result = await loader.loadRows(5, 1);
      const row = result.rows[0];

      expect(typeof row.data.id).toBe('number');
      expect(typeof row.data.name).toBe('string');
      expect(typeof row.data.value).toBe('number');
      expect(typeof row.data.active).toBe('boolean');
      expect(Array.isArray(row.data.tags)).toBe(true);
    });

    test('maintains data consistency across batches', async () => {
      const batch1 = await loader.loadRows(0, 50);
      const batch2 = await loader.loadRows(0, 100);

      // First 50 rows should be identical
      for (let i = 0; i < 50; i++) {
        expect(batch2.rows[i].data).toEqual(batch1.rows[i].data);
      }
    });
  });

  describe('nested structures', () => {
    test('handles nested Parquet structures', async () => {
      const nestedPath = path.join(process.cwd(), 'test-data', 'nested.parquet');
      await loader.initialize(nestedPath);

      const metadata = await loader.getMetadata();
      expect(metadata.totalRows).toBe(100);

      const result = await loader.loadRows(0, 10);
      result.rows.forEach(row => {
        expect(row.data).toBeDefined();
        expect(row.data.id).toBeDefined();
        expect(row.data.user).toBeDefined();
      });
    });
  });
});
