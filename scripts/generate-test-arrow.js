const fs = require('fs');
const path = require('path');
const arrow = require('apache-arrow');

/**
 * Generate Arrow IPC test files for unit testing
 *
 * Creates:
 * - test.arrow (1000 rows with mixed types)
 * - test.feather (1000 rows, Feather format)
 * - large.arrow (100k rows for performance testing)
 * - nested.arrow (rows with nested structures)
 */

// Ensure test-data directory exists
const testDataDir = path.join(process.cwd(), 'test-data');
if (!fs.existsSync(testDataDir)) {
    fs.mkdirSync(testDataDir);
}

console.log('Generating Arrow IPC test files...');

// Helper to create table with sample data
function createSampleTable(numRows) {
    // Create sample data arrays
    const ids = Int32Array.from({ length: numRows }, (_, i) => i);
    const names = Array.from({ length: numRows }, (_, i) => `User ${i}`);
    const ages = Int32Array.from({ length: numRows }, (_, i) => 20 + (i % 50));
    const scores = Float64Array.from({ length: numRows }, (_, i) => (i % 100) / 10.0);
    const active = Array.from({ length: numRows }, (_, i) => i % 2 === 0);
    const descriptions = Array.from({ length: numRows }, (_, i) => `Description for row ${i}`);

    // Create Arrow table with explicit types
    const table = arrow.tableFromArrays({
        id: ids,
        name: names,
        age: ages,
        score: scores,
        active: active,
        description: descriptions
    });

    return table;
}

// Helper to create table with nested structures
function createNestedTable(numRows) {
    const ids = Int32Array.from({ length: numRows }, (_, i) => i);
    const names = Array.from({ length: numRows }, (_, i) => `User ${i}`);

    // Create nested data
    const metadata = Array.from({ length: numRows }, (_, i) => ({
        created_at: new Date(2024, 0, i % 30 + 1).toISOString(),
        tags: [`tag${i % 5}`, `tag${(i + 1) % 5}`],
        settings: {
            theme: i % 2 === 0 ? 'dark' : 'light',
            notifications: i % 3 === 0
        }
    }));

    // Create table with struct column
    const table = arrow.tableFromArrays({
        id: ids,
        name: names,
        metadata: metadata.map(m => JSON.stringify(m)) // Store as string for simplicity
    });

    return table;
}

// 1. Generate test.arrow (1000 rows)
console.log('Creating test.arrow (1000 rows)...');
const testTable = createSampleTable(1000);
const testArrowPath = path.join(testDataDir, 'test.arrow');
fs.writeFileSync(testArrowPath, arrow.tableToIPC(testTable));
console.log(`✓ Created ${testArrowPath} (${(fs.statSync(testArrowPath).size / 1024).toFixed(2)} KB)`);

// 2. Generate test.feather (1000 rows) - same format, different extension
console.log('Creating test.feather (1000 rows)...');
const testFeatherPath = path.join(testDataDir, 'test.feather');
fs.writeFileSync(testFeatherPath, arrow.tableToIPC(testTable));
console.log(`✓ Created ${testFeatherPath} (${(fs.statSync(testFeatherPath).size / 1024).toFixed(2)} KB)`);

// 3. Generate large.arrow (100k rows for performance testing)
console.log('Creating large.arrow (100k rows)...');
const largeTable = createSampleTable(100000);
const largeArrowPath = path.join(testDataDir, 'large.arrow');
fs.writeFileSync(largeArrowPath, arrow.tableToIPC(largeTable));
console.log(`✓ Created ${largeArrowPath} (${(fs.statSync(largeArrowPath).size / 1024 / 1024).toFixed(2)} MB)`);

// 4. Generate nested.arrow (100 rows with nested structures)
console.log('Creating nested.arrow (100 rows with nested data)...');
const nestedTable = createNestedTable(100);
const nestedArrowPath = path.join(testDataDir, 'nested.arrow');
fs.writeFileSync(nestedArrowPath, arrow.tableToIPC(nestedTable));
console.log(`✓ Created ${nestedArrowPath} (${(fs.statSync(nestedArrowPath).size / 1024).toFixed(2)} KB)`);

// 5. Generate empty.arrow (0 rows)
console.log('Creating empty.arrow (0 rows)...');
const emptyTable = createSampleTable(0);
const emptyArrowPath = path.join(testDataDir, 'empty.arrow');
fs.writeFileSync(emptyArrowPath, arrow.tableToIPC(emptyTable));
console.log(`✓ Created ${emptyArrowPath} (${fs.statSync(emptyArrowPath).size} bytes)`);

// 6. Generate single-row.arrow (1 row)
console.log('Creating single-row.arrow (1 row)...');
const singleTable = createSampleTable(1);
const singleArrowPath = path.join(testDataDir, 'single-row.arrow');
fs.writeFileSync(singleArrowPath, arrow.tableToIPC(singleTable));
console.log(`✓ Created ${singleArrowPath} (${fs.statSync(singleArrowPath).size} bytes)`);

// Print summary
console.log('\n✨ Successfully generated all Arrow IPC test files!');
console.log('\nGenerated files:');
console.log('  - test.arrow (1000 rows, mixed types)');
console.log('  - test.feather (1000 rows, Feather format)');
console.log('  - large.arrow (100k rows, performance testing)');
console.log('  - nested.arrow (100 rows, nested structures)');
console.log('  - empty.arrow (0 rows, edge case)');
console.log('  - single-row.arrow (1 row, edge case)');
console.log('\nRun tests with: npm test');
