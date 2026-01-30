/**
 * Script to generate test Parquet files for unit testing
 * Run with: node scripts/generate-test-parquet.js
 */

const parquet = require('@dsnp/parquetjs');
const fs = require('fs');
const path = require('path');

// Ensure test-data directory exists
const testDataDir = path.join(__dirname, '..', 'test-data');
if (!fs.existsSync(testDataDir)) {
    fs.mkdirSync(testDataDir, { recursive: true });
}

async function generateTestParquet() {
    console.log('Generating test.parquet (1000 rows)...');

    // Define schema
    const schema = new parquet.ParquetSchema({
        id: { type: 'INT32' },
        name: { type: 'UTF8' },
        value: { type: 'DOUBLE' },
        active: { type: 'BOOLEAN' },
        tags: { type: 'UTF8', repeated: true },  // Array of strings
    });

    // Create writer
    const writer = await parquet.ParquetWriter.openFile(schema, path.join(testDataDir, 'test.parquet'));

    // Write 1000 rows
    for (let i = 0; i < 1000; i++) {
        await writer.appendRow({
            id: i,
            name: `User ${i}`,
            value: i * 1.5,
            active: i % 2 === 0,
            tags: [`tag${i}`, `category${i % 10}`]
        });
    }

    await writer.close();
    console.log('✓ test.parquet created (1000 rows)');
}

async function generateLargeParquet() {
    console.log('Generating large.parquet (100,000 rows)...');

    // Define schema
    const schema = new parquet.ParquetSchema({
        id: { type: 'INT64' },
        text: { type: 'UTF8' },
        timestamp: { type: 'TIMESTAMP_MILLIS' },
    });

    // Create writer
    const writer = await parquet.ParquetWriter.openFile(schema, path.join(testDataDir, 'large.parquet'));

    // Write 100,000 rows
    for (let i = 0; i < 100000; i++) {
        await writer.appendRow({
            id: i,
            text: `Large file row ${i}`,
            timestamp: Date.now() + i * 1000
        });

        if (i % 10000 === 0) {
            console.log(`  Written ${i} rows...`);
        }
    }

    await writer.close();
    console.log('✓ large.parquet created (100,000 rows)');
}

async function generateNestedParquet() {
    console.log('Generating nested.parquet (100 rows with nested structure)...');

    // Define schema with nested structure
    const schema = new parquet.ParquetSchema({
        id: { type: 'INT32' },
        user: {
            fields: {
                name: { type: 'UTF8' },
                email: { type: 'UTF8' },
            }
        },
        scores: { type: 'INT32', repeated: true }
    });

    // Create writer
    const writer = await parquet.ParquetWriter.openFile(schema, path.join(testDataDir, 'nested.parquet'));

    // Write 100 rows with nested data
    for (let i = 0; i < 100; i++) {
        await writer.appendRow({
            id: i,
            user: {
                name: `User ${i}`,
                email: `user${i}@example.com`
            },
            scores: [i, i * 2, i * 3]
        });
    }

    await writer.close();
    console.log('✓ nested.parquet created (100 rows with nested structure)');
}

async function main() {
    try {
        await generateTestParquet();
        await generateLargeParquet();
        await generateNestedParquet();
        console.log('\n✓ All test Parquet files generated successfully!');
    } catch (error) {
        console.error('Error generating test files:', error);
        process.exit(1);
    }
}

main();
