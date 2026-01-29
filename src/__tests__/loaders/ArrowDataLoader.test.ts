import * as path from 'path';
import { ArrowDataLoader } from '../../formats/loaders/ArrowDataLoader';
import { DataType } from '../../formats/interfaces';

describe('ArrowDataLoader', () => {
  let loader: ArrowDataLoader;

  beforeEach(() => {
    loader = new ArrowDataLoader();
  });

  afterEach(() => {
    loader.dispose();
  });

  describe('initialize', () => {
    test('initializes with valid Arrow file', async () => {
      const arrowPath = path.join(process.cwd(), 'test-data', 'test.arrow');
      await loader.initialize(arrowPath);
      const metadata = await loader.getMetadata();
      expect(metadata.format).toBe('arrow');
      expect(metadata.fileSizeBytes).toBeGreaterThan(0);
      expect(metadata.totalRows).toBe(1000);
    });

    test('initializes with valid Feather file', async () => {
      const featherPath = path.join(process.cwd(), 'test-data', 'test.feather');
      await loader.initialize(featherPath);
      const metadata = await loader.getMetadata();
      expect(metadata.format).toBe('feather');
      expect(metadata.fileSizeBytes).toBeGreaterThan(0);
      expect(metadata.totalRows).toBe(1000);
    });

    test('extracts schema correctly', async () => {
      const arrowPath = path.join(process.cwd(), 'test-data', 'test.arrow');
      await loader.initialize(arrowPath);
      const metadata = await loader.getMetadata();

      expect(metadata.schema).toBeDefined();
      expect(metadata.schema?.columns).toBeDefined();
      expect(metadata.schema!.columns.length).toBeGreaterThan(0);

      // Check specific columns
      const columnNames = metadata.schema!.columns.map(c => c.name);
      expect(columnNames).toContain('id');
      expect(columnNames).toContain('name');
      expect(columnNames).toContain('age');
      expect(columnNames).toContain('score');
      expect(columnNames).toContain('active');
      expect(columnNames).toContain('description');
    });

    test('column types are mapped correctly', async () => {
      const arrowPath = path.join(process.cwd(), 'test-data', 'test.arrow');
      await loader.initialize(arrowPath);
      const metadata = await loader.getMetadata();

      const columns = metadata.schema!.columns;
      const idCol = columns.find(c => c.name === 'id');
      const nameCol = columns.find(c => c.name === 'name');
      const ageCol = columns.find(c => c.name === 'age');
      const scoreCol = columns.find(c => c.name === 'score');
      const activeCol = columns.find(c => c.name === 'active');

      expect(idCol?.type).toBe(DataType.INT32);
      expect(nameCol?.type).toBe(DataType.STRING);
      expect(ageCol?.type).toBe(DataType.INT32);
      expect(scoreCol?.type).toBe(DataType.FLOAT); // Float64Array creates generic Float type
      expect(activeCol?.type).toBe(DataType.BOOLEAN);
    });

    test('throws error for non-existent file', async () => {
      await expect(loader.initialize('/nonexistent/file.arrow'))
        .rejects.toThrow();
    });
  });

  describe('getMetadata', () => {
    test('throws error if not initialized', async () => {
      await expect(loader.getMetadata()).rejects.toThrow(/not initialized/i);
    });

    test('returns correct metadata for Arrow file', async () => {
      const arrowPath = path.join(process.cwd(), 'test-data', 'test.arrow');
      await loader.initialize(arrowPath);
      const metadata = await loader.getMetadata();

      expect(metadata.format).toBe('arrow');
      expect(metadata.fileSizeBytes).toBeGreaterThan(0);
      expect(metadata.totalRows).toBe(1000);
      expect(metadata.schema).toBeDefined();
    });

    test('returns correct metadata for Feather file', async () => {
      const featherPath = path.join(process.cwd(), 'test-data', 'test.feather');
      await loader.initialize(featherPath);
      const metadata = await loader.getMetadata();

      expect(metadata.format).toBe('feather');
      expect(metadata.fileSizeBytes).toBeGreaterThan(0);
      expect(metadata.totalRows).toBe(1000);
    });
  });

  describe('loadRows', () => {
    beforeEach(async () => {
      const arrowPath = path.join(process.cwd(), 'test-data', 'test.arrow');
      await loader.initialize(arrowPath);
    });

    test('throws error if not initialized', async () => {
      const uninitLoader = new ArrowDataLoader();
      await expect(uninitLoader.loadRows(0, 100))
        .rejects.toThrow(/not initialized/i);
    });

    test('loads first 100 rows', async () => {
      const result = await loader.loadRows(0, 100);

      expect(result.rows).toHaveLength(100);
      expect(result.rows[0].index).toBe(0);
      expect(result.hasMore).toBe(true);
      expect(result.nextOffset).toBe(100);
    });

    test('handles pagination correctly', async () => {
      const batch1 = await loader.loadRows(0, 10);
      const batch2 = await loader.loadRows(10, 10);

      expect(batch1.rows).toHaveLength(10);
      expect(batch2.rows).toHaveLength(10);
      expect(batch2.rows[0].index).toBe(10);
      expect(batch1.rows[0].data.id).toBe(0);
      expect(batch2.rows[0].data.id).toBe(10);
    });

    test('parses row data correctly', async () => {
      const result = await loader.loadRows(0, 1);
      const row = result.rows[0];

      expect(row.data).toBeDefined();
      expect(row.data.id).toBe(0);
      expect(row.data.name).toBe('User 0');
      expect(row.data.age).toBe(20);
      expect(typeof row.data.score).toBe('number');
      expect(typeof row.data.active).toBe('boolean');
      expect(typeof row.data.description).toBe('string');
    });

    test('includes raw JSON representation', async () => {
      const result = await loader.loadRows(0, 1);
      const row = result.rows[0];

      expect(row.raw).toBeDefined();
      expect(typeof row.raw).toBe('string');
      const parsed = JSON.parse(row.raw!);
      expect(parsed).toEqual(row.data);
    });

    test('handles offset beyond file end', async () => {
      const result = await loader.loadRows(10000, 100);

      expect(result.rows).toHaveLength(0);
      expect(result.hasMore).toBe(false);
      expect(result.nextOffset).toBe(1000);
    });

    test('returns correct nextOffset', async () => {
      const result = await loader.loadRows(50, 75);

      expect(result.nextOffset).toBe(125);
    });

    test('hasMore is false when reaching end of file', async () => {
      const result = await loader.loadRows(950, 100);

      expect(result.rows.length).toBeLessThanOrEqual(50);
      expect(result.hasMore).toBe(false);
    });

    test('handles exact end of file', async () => {
      const result = await loader.loadRows(900, 100);

      expect(result.rows).toHaveLength(100);
      expect(result.hasMore).toBe(false);
      expect(result.nextOffset).toBe(1000);
    });
  });

  describe('search filtering', () => {
    beforeEach(async () => {
      const arrowPath = path.join(process.cwd(), 'test-data', 'test.arrow');
      await loader.initialize(arrowPath);
    });

    test('supports search filtering', async () => {
      const result = await loader.loadRows(0, 100, { searchTerm: 'User 5' });

      // Should match "User 5", "User 50", "User 51", ..., "User 59", "User 500", ...
      expect(result.rows.length).toBeGreaterThan(0);
      result.rows.forEach(row => {
        const rowText = JSON.stringify(row.data).toLowerCase();
        expect(rowText).toContain('user 5');
      });
    });

    test('returns empty array when no matches', async () => {
      const result = await loader.loadRows(0, 100, { searchTerm: 'NONEXISTENT_STRING_XYZ' });

      expect(result.rows).toHaveLength(0);
    });

    test('search is case-insensitive', async () => {
      const result = await loader.loadRows(0, 100, { searchTerm: 'USER 5' });

      expect(result.rows.length).toBeGreaterThan(0);
      result.rows.forEach(row => {
        const rowText = JSON.stringify(row.data).toLowerCase();
        expect(rowText).toContain('user 5');
      });
    });
  });

  describe('jumpToRow', () => {
    beforeEach(async () => {
      const arrowPath = path.join(process.cwd(), 'test-data', 'test.arrow');
      await loader.initialize(arrowPath);
    });

    test('jumps to specific row', async () => {
      const result = await loader.jumpToRow(500);

      expect(result.rows.length).toBeGreaterThan(0);
      expect(result.rows[0].index).toBe(500);
      expect(result.rows[0].data.id).toBe(500);
    });

    test('jumps to row near end of file', async () => {
      const result = await loader.jumpToRow(950);

      expect(result.rows.length).toBeGreaterThan(0);
      expect(result.rows[0].index).toBe(950);
      expect(result.rows[0].data.id).toBe(950);
    });

    test('handles jump beyond file end', async () => {
      const result = await loader.jumpToRow(5000);

      expect(result.rows).toHaveLength(0);
      expect(result.hasMore).toBe(false);
    });
  });

  describe('extractTextForTokens', () => {
    test('converts row data to JSON string', () => {
      const row = { id: 1, name: 'Test', value: 123 };
      const text = loader.extractTextForTokens(row);

      expect(text).toBe(JSON.stringify(row));
    });

    test('handles string input', () => {
      const text = loader.extractTextForTokens('test string');

      expect(text).toBe('test string');
    });

    test('handles nested objects', () => {
      const row = { id: 1, nested: { field1: 'value', field2: 123 } };
      const text = loader.extractTextForTokens(row);

      expect(text).toBe(JSON.stringify(row));
    });
  });

  describe('memory efficiency', () => {
    test('does not load entire file into memory', async () => {
      const largePath = path.join(process.cwd(), 'test-data', 'large.arrow');
      await loader.initialize(largePath);

      const memBefore = process.memoryUsage().heapUsed;
      await loader.loadRows(0, 100);
      const memAfter = process.memoryUsage().heapUsed;

      // Memory increase should be minimal (< 50MB)
      const memDelta = (memAfter - memBefore) / 1024 / 1024;
      expect(memDelta).toBeLessThan(50);
    });

    test('handles multiple sequential loads without accumulation', async () => {
      const arrowPath = path.join(process.cwd(), 'test-data', 'test.arrow');
      await loader.initialize(arrowPath);

      const memBefore = process.memoryUsage().heapUsed;

      // Load multiple batches
      for (let i = 0; i < 10; i++) {
        await loader.loadRows(i * 100, 100);
      }

      const memAfter = process.memoryUsage().heapUsed;
      const memDelta = (memAfter - memBefore) / 1024 / 1024;

      // Memory shouldn't accumulate significantly
      expect(memDelta).toBeLessThan(20);
    });
  });

  describe('edge cases', () => {
    test('handles empty Arrow file', async () => {
      const emptyPath = path.join(process.cwd(), 'test-data', 'empty.arrow');
      await loader.initialize(emptyPath);

      const metadata = await loader.getMetadata();
      expect(metadata.totalRows).toBe(0);

      const result = await loader.loadRows(0, 100);
      expect(result.rows).toHaveLength(0);
      expect(result.hasMore).toBe(false);
    });

    test('handles single-row Arrow file', async () => {
      const singlePath = path.join(process.cwd(), 'test-data', 'single-row.arrow');
      await loader.initialize(singlePath);

      const metadata = await loader.getMetadata();
      expect(metadata.totalRows).toBe(1);

      const result = await loader.loadRows(0, 100);
      expect(result.rows).toHaveLength(1);
      expect(result.hasMore).toBe(false);
      expect(result.rows[0].index).toBe(0);
    });

    test('handles nested structures', async () => {
      const nestedPath = path.join(process.cwd(), 'test-data', 'nested.arrow');
      await loader.initialize(nestedPath);

      const result = await loader.loadRows(0, 10);
      expect(result.rows.length).toBeGreaterThan(0);

      // Verify nested data is accessible
      const row = result.rows[0];
      expect(row.data).toBeDefined();
      expect(row.data.id).toBeDefined();
      expect(row.data.name).toBeDefined();
      expect(row.data.metadata).toBeDefined();
    });
  });

  describe('data integrity', () => {
    beforeEach(async () => {
      const arrowPath = path.join(process.cwd(), 'test-data', 'test.arrow');
      await loader.initialize(arrowPath);
    });

    test('preserves zero-based indexing', async () => {
      const result = await loader.loadRows(0, 10);

      expect(result.rows[0].index).toBe(0);
      expect(result.rows[9].index).toBe(9);
    });

    test('maintains data consistency across batches', async () => {
      const batch1 = await loader.loadRows(0, 50);
      const batch2 = await loader.loadRows(50, 50);

      // Last row of batch1 and first row of batch2 should be sequential
      expect(batch1.rows[49].index).toBe(49);
      expect(batch2.rows[0].index).toBe(50);

      // Data IDs should match indices
      expect(batch1.rows[49].data.id).toBe(49);
      expect(batch2.rows[0].data.id).toBe(50);
    });

    test('maintains consistent row structure', async () => {
      const result = await loader.loadRows(0, 100);

      result.rows.forEach(row => {
        expect(row.index).toBeDefined();
        expect(row.data).toBeDefined();
        expect(row.raw).toBeDefined();
        expect(typeof row.index).toBe('number');
        expect(typeof row.data).toBe('object');
        expect(typeof row.raw).toBe('string');
      });
    });
  });

  describe('dispose', () => {
    test('cleans up resources', async () => {
      const arrowPath = path.join(process.cwd(), 'test-data', 'test.arrow');
      await loader.initialize(arrowPath);

      loader.dispose();

      // Should be able to call dispose multiple times
      expect(() => loader.dispose()).not.toThrow();
    });
  });
});
