# Bread Dataset Viewer

View massive dataset files instantly. No freezing, no crashes, no terminal commands.

![Bread Dataset Viewer Screenshot](https://raw.githubusercontent.com/Bread-Technologies/mle_vscode_extension/main/screenshot.png)

## Stop Fighting With Large Files

Tired of VS Code freezing when you open a 5GB JSONL file? Done squinting at `tail` output in Terminal? This extension opens dataset files of any size instantly by lazy-loading only what you need.

**Open files up to 100GB+ without breaking a sweat.**

## Supported Formats

- **JSONL** (JSON Lines) - ML training datasets, logs
- **JSON** - Regular JSON files
- **CSV/TSV** - Spreadsheets, tabular data
- **Parquet** - Columnar data format
- **Arrow/Feather** - In-memory data format

## Key Features

### 🚀 Instant Loading (The Main Thing)

Click any dataset file and it opens immediately. No loading bars, no beach balls, no crashed editor. Jump to line 50,000 in a 10GB file without loading the entire thing into memory.

### 🔢 Token Counting for ML Data

See exact token counts using real model tokenizers. Perfect for ML engineers working with training data who need to know token usage.

**Supported tokenizers**: Qwen 3.x, DeepSeek V3, Llama 3.x, Gemini, Mistral, Phi-4, GPT-4o, Claude, and more.

Works with chat templates for accurate multi-turn conversation token counts.

### 📊 Multiple View Modes

- **Pretty View**: Collapsible JSON trees with syntax highlighting
- **Render View**: Chat messages with markdown and LaTeX rendering
- **Table View**: Spreadsheet-style columns (great for CSV/Parquet)
- **Raw View**: Plain text with line numbers

### 🔍 Search & Navigation

- Search across records by content
- Jump to any line number instantly
- Filter nested JSON fields (path filtering)
- Load more records on demand

## How to Use

1. Install the extension
2. Click any `.jsonl`, `.json`, `.csv`, `.parquet`, or `.arrow` file
3. The viewer opens automatically

Switch views with the buttons at the top. Use the tokenizer dropdown to see token counts. Search or jump to specific lines as needed.

## Why You Need This

If you work with ML datasets, logs, or any large structured data files, you've hit this wall: VS Code can't handle files over ~50MB without choking. You end up using `cat`, `head`, `tail`, or writing one-off Python scripts just to peek at your data.

This extension fixes that. It's built specifically for viewing large files that would normally crash your editor. The token counting is a bonus for ML folks who need accurate counts without firing up a Python REPL every time.

## Requirements

VS Code 1.85.0 or higher

## License

MIT

**Note on Bundled Tokenizers**: This extension includes tokenizer files from various HuggingFace models for offline token counting. Each tokenizer retains its original license from the source model. See `/tokenizers/MANIFEST.md` for details.
