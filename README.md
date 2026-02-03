# Bread Dataset Viewer

A VS Code extension for viewing large dataset files with lazy loading and token counting.

![Bread Dataset Viewer Screenshot](https://raw.githubusercontent.com/Bread-Technologies/mle_vscode_extension/main/screenshot.png)

## What It Does

Opens JSONL, CSV, Parquet, and Arrow files of any size by streaming and lazy-loading data. Includes token counting with real model tokenizers for ML training datasets.

VS Code normally crashes or freezes when opening files over 50MB. This extension handles files up to 100GB+ by only loading what's visible.

## Supported Formats

- JSONL (JSON Lines)
- JSON
- CSV/TSV
- Parquet
- Arrow/Feather

## Features

**Lazy Loading**
Opens large files instantly by loading data on-demand. Jump to any line without loading the entire file into memory.

**Token Counting**
Shows exact token counts using real tokenizers from Qwen, DeepSeek, Llama, GPT, Claude, Mistral, Phi, and others. Supports chat templates for multi-turn conversations.

**Multiple Views**
- Pretty: Collapsible JSON trees
- Render: Chat messages with markdown/LaTeX
- Table: Spreadsheet columns
- Raw: Plain text with line numbers

**Search and Navigation**
Search by content, jump to line numbers, filter JSON paths, and load more records as needed.

## Usage

Install the extension and click any supported file. The viewer opens automatically. Use the toolbar to switch views, select tokenizers, or search.

For ML work: Pick a tokenizer from the dropdown to see accurate token counts for your training data.

## Requirements

VS Code 1.85.0 or higher

## License

MIT

**Note on Bundled Tokenizers**: This extension includes tokenizer files from various HuggingFace models for offline token counting. Each tokenizer retains its original license from the source model. See `/tokenizers/MANIFEST.md` for details.
