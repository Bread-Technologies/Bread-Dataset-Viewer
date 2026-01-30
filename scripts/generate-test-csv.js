/**
 * Script to generate test CSV files for unit testing
 * Run with: node scripts/generate-test-csv.js
 */

const fs = require('fs');
const path = require('path');

// Ensure test-data directory exists
const testDataDir = path.join(__dirname, '..', 'test-data');
if (!fs.existsSync(testDataDir)) {
    fs.mkdirSync(testDataDir, { recursive: true });
}

function generateTestCSV() {
    console.log('Generating test.csv (1000 rows with headers)...');

    const filePath = path.join(testDataDir, 'test.csv');
    const stream = fs.createWriteStream(filePath);

    // Write header
    stream.write('id,name,value,description\n');

    // Write 1000 rows
    for (let i = 0; i < 1000; i++) {
        stream.write(`${i},User ${i},${i * 100},Description for row ${i}\n`);
    }

    stream.end();
    console.log('✓ test.csv created (1000 rows)');
}

function generateTestTSV() {
    console.log('Generating test.tsv (1000 rows tab-delimited)...');

    const filePath = path.join(testDataDir, 'test.tsv');
    const stream = fs.createWriteStream(filePath);

    // Write header
    stream.write('id\tname\tvalue\n');

    // Write 1000 rows
    for (let i = 0; i < 1000; i++) {
        stream.write(`${i}\tUser ${i}\t${i * 100}\n`);
    }

    stream.end();
    console.log('✓ test.tsv created (1000 rows)');
}

function generateQuotedCSV() {
    console.log('Generating quoted.csv (with commas in quoted fields)...');

    const filePath = path.join(testDataDir, 'quoted.csv');
    const content = `id,name,address
1,"John Doe","123 Main St, Apt 4, New York, NY"
2,"Jane Smith","456 Oak Ave, Suite 100, Los Angeles, CA"
3,"Bob Johnson","789 Pine Rd, Unit 5, Chicago, IL"
4,"Alice Brown","321 Elm St, Floor 2, Houston, TX"
5,"Charlie Wilson","654 Maple Dr, Building A, Phoenix, AZ"
`;

    fs.writeFileSync(filePath, content);
    console.log('✓ quoted.csv created (5 rows with quoted fields)');
}

function generateEscapedQuotesCSV() {
    console.log('Generating escaped-quotes.csv (with escaped quotes)...');

    const filePath = path.join(testDataDir, 'escaped-quotes.csv');
    const content = `id,quote,source
1,"He said ""Hello"" to me",Book
2,"She replied ""Hi there""",Article
3,"The sign read ""Welcome""",Sign
`;

    fs.writeFileSync(filePath, content);
    console.log('✓ escaped-quotes.csv created (3 rows with escaped quotes)');
}

function generateSemicolonCSV() {
    console.log('Generating test-semicolon.csv (semicolon delimiter)...');

    const filePath = path.join(testDataDir, 'test-semicolon.csv');
    const stream = fs.createWriteStream(filePath);

    // Write header
    stream.write('id;name;value\n');

    // Write 100 rows
    for (let i = 0; i < 100; i++) {
        stream.write(`${i};User ${i};${i * 100}\n`);
    }

    stream.end();
    console.log('✓ test-semicolon.csv created (100 rows)');
}

function generateLargeCSV() {
    console.log('Generating large.csv (100,000 rows for memory testing)...');

    const filePath = path.join(testDataDir, 'large.csv');
    const stream = fs.createWriteStream(filePath);

    // Write header
    stream.write('id,text,value\n');

    // Write 100,000 rows
    for (let i = 0; i < 100000; i++) {
        stream.write(`${i},Text for row ${i},${i * 100}\n`);

        if (i % 10000 === 0) {
            console.log(`  Written ${i} rows...`);
        }
    }

    stream.end();
    console.log('✓ large.csv created (100,000 rows)');
}

async function main() {
    try {
        generateTestCSV();
        generateTestTSV();
        generateQuotedCSV();
        generateEscapedQuotesCSV();
        generateSemicolonCSV();
        generateLargeCSV();
        console.log('\n✓ All test CSV files generated successfully!');
    } catch (error) {
        console.error('Error generating test files:', error);
        process.exit(1);
    }
}

main();
