import * as path from 'path';
import { CsvDataLoader } from '../../formats/loaders/CsvDataLoader';
import { DataType } from '../../formats/interfaces';

describe('CsvDataLoader', () => {
  let loader: CsvDataLoader;

  beforeEach(() => {
    loader = new CsvDataLoader();
  });

  afterEach(() => {
    loader.dispose();
  });

  describe('initialize', () => {
    test('initializes with valid CSV file', async () => {
      const csvPath = path.join(process.cwd(), 'test-data', 'test.csv');
      await loader.initialize(csvPath);
      const metadata = await loader.getMetadata();
      expect(metadata.format).toBe('csv');
      expect(metadata.fileSizeBytes).toBeGreaterThan(0);
    });

    test('initializes with valid TSV file', async () => {
      const tsvPath = path.join(process.cwd(), 'test-data', 'test.tsv');
      await loader.initialize(tsvPath);
      const metadata = await loader.getMetadata();
      expect(metadata.format).toBe('tsv');
      expect(metadata.fileSizeBytes).toBeGreaterThan(0);
    });

    test('throws error for non-existent file', async () => {
      await expect(loader.initialize('/nonexistent.csv')).rejects.toThrow();
    });
  });

  describe('delimiter detection', () => {
    test('detects comma delimiter', async () => {
      const csvPath = path.join(process.cwd(), 'test-data', 'test.csv');
      await loader.initialize(csvPath);
      const metadata = await loader.getMetadata();
      expect(metadata.format).toBe('csv');
    });

    test('detects tab delimiter', async () => {
      const tsvPath = path.join(process.cwd(), 'test-data', 'test.tsv');
      await loader.initialize(tsvPath);
      const metadata = await loader.getMetadata();
      expect(metadata.format).toBe('tsv');
    });

    test('detects semicolon delimiter', async () => {
      const semiPath = path.join(process.cwd(), 'test-data', 'test-semicolon.csv');
      await loader.initialize(semiPath);
      const metadata = await loader.getMetadata();
      // Should work correctly even with semicolon delimiter
      expect(metadata.schema?.columns).toBeDefined();
      expect(metadata.schema?.columns.length).toBe(3);
    });
  });

  describe('header detection', () => {
    test('extracts headers correctly from CSV', async () => {
      const csvPath = path.join(process.cwd(), 'test-data', 'test.csv');
      await loader.initialize(csvPath);
      const metadata = await loader.getMetadata();

      expect(metadata.schema).toBeDefined();
      if (!metadata.schema) {
        throw new Error('Schema is undefined');
      }

      expect(metadata.schema.columns).toBeDefined();
      expect(metadata.schema.columns.length).toBe(4);

      const columnNames = metadata.schema.columns.map(c => c.name);
      expect(columnNames).toContain('id');
      expect(columnNames).toContain('name');
      expect(columnNames).toContain('value');
      expect(columnNames).toContain('description');
    });

    test('extracts headers correctly from TSV', async () => {
      const tsvPath = path.join(process.cwd(), 'test-data', 'test.tsv');
      await loader.initialize(tsvPath);
      const metadata = await loader.getMetadata();

      expect(metadata.schema).toBeDefined();
      if (!metadata.schema) {
        throw new Error('Schema is undefined');
      }

      const columnNames = metadata.schema.columns.map(c => c.name);
      expect(columnNames).toContain('id');
      expect(columnNames).toContain('name');
      expect(columnNames).toContain('value');
    });

    test('all columns have STRING type', async () => {
      const csvPath = path.join(process.cwd(), 'test-data', 'test.csv');
      await loader.initialize(csvPath);
      const metadata = await loader.getMetadata();

      if (!metadata.schema) {
        throw new Error('Schema is undefined');
      }

      metadata.schema.columns.forEach(col => {
        expect(col.type).toBe(DataType.STRING);
        expect(col.nullable).toBe(true);
      });
    });
  });

  describe('loadRows', () => {
    beforeEach(async () => {
      const csvPath = path.join(process.cwd(), 'test-data', 'test.csv');
      await loader.initialize(csvPath);
    });

    test('loads first 100 rows', async () => {
      const result = await loader.loadRows(0, 100);
      expect(result.rows.length).toBeLessThanOrEqual(100);
      expect(result.rows[0].index).toBe(0);
      expect(result.hasMore).toBe(true);
      expect(result.nextOffset).toBe(100);
    });

    test('handles pagination correctly', async () => {
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
      expect(row.data.id).toBe('0');
      expect(row.data.name).toBe('User 0');
      expect(row.data.value).toBe('0');
      expect(row.data.description).toBe('Description for row 0');
    });

    test('includes raw CSV line', async () => {
      const result = await loader.loadRows(0, 1);
      const row = result.rows[0];

      expect(row.raw).toBeDefined();
      expect(row.raw).toContain('0');
      expect(row.raw).toContain('User 0');
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

  describe('quoted fields', () => {
    test('handles quoted fields with commas', async () => {
      const quotedPath = path.join(process.cwd(), 'test-data', 'quoted.csv');
      await loader.initialize(quotedPath);
      const result = await loader.loadRows(0, 10);

      // Verify quoted fields are parsed correctly
      result.rows.forEach(row => {
        expect(row.data).toBeDefined();
        expect(row.data.name).toBeDefined();
        expect(row.data.address).toBeDefined();
        // Address should contain commas but be parsed as single field
        expect(row.data.address).toContain(',');
      });
    });

    test('handles escaped quotes (double quotes)', async () => {
      const escapedPath = path.join(process.cwd(), 'test-data', 'escaped-quotes.csv');
      await loader.initialize(escapedPath);
      const result = await loader.loadRows(0, 10);

      // Should handle "" correctly
      expect(result.rows.length).toBeGreaterThan(0);
      result.rows.forEach(row => {
        expect(row.data).toBeDefined();
        expect(row.data.quote).toBeDefined();
      });
    });
  });

  describe('search filtering', () => {
    beforeEach(async () => {
      const csvPath = path.join(process.cwd(), 'test-data', 'test.csv');
      await loader.initialize(csvPath);
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

    test('returns empty array when no matches', async () => {
      const result = await loader.loadRows(0, 100, { searchTerm: 'NONEXISTENT' });
      expect(result.rows).toHaveLength(0);
    });
  });

  describe('jumpToRow', () => {
    beforeEach(async () => {
      const csvPath = path.join(process.cwd(), 'test-data', 'test.csv');
      await loader.initialize(csvPath);
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
      const row = { id: '1', name: 'Test', value: '123.45' };
      const text = loader.extractTextForTokens(row);
      expect(text).toBe(JSON.stringify(row));
    });

    test('handles string input', () => {
      const text = loader.extractTextForTokens('id,name,value');
      expect(text).toBe('id,name,value');
    });
  });

  describe('memory efficiency', () => {
    test('does not load entire file into memory', async () => {
      const largePath = path.join(process.cwd(), 'test-data', 'large.csv');
      await loader.initialize(largePath);

      const memBefore = process.memoryUsage().heapUsed;
      await loader.loadRows(0, 100);
      const memAfter = process.memoryUsage().heapUsed;

      // Memory increase should be minimal (< 20MB)
      const memDelta = (memAfter - memBefore) / 1024 / 1024; // MB
      expect(memDelta).toBeLessThan(20);
    });

    test('handles multiple sequential loads without accumulation', async () => {
      const csvPath = path.join(process.cwd(), 'test-data', 'test.csv');
      await loader.initialize(csvPath);

      const memBefore = process.memoryUsage().heapUsed;

      // Load 10 batches sequentially
      for (let i = 0; i < 10; i++) {
        await loader.loadRows(i * 100, 100);
      }

      const memAfter = process.memoryUsage().heapUsed;
      const memDelta = (memAfter - memBefore) / 1024 / 1024; // MB

      // Memory should not accumulate significantly (allow 10MB for GC timing)
      expect(memDelta).toBeLessThan(10);
    });
  });

  describe('data integrity', () => {
    beforeEach(async () => {
      const csvPath = path.join(process.cwd(), 'test-data', 'test.csv');
      await loader.initialize(csvPath);
    });

    test('preserves zero-based indexing', async () => {
      const result = await loader.loadRows(0, 10);
      expect(result.rows[0].index).toBe(0);
      expect(result.rows[9].index).toBe(9);
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
});
