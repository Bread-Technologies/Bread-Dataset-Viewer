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

## Privacy & Telemetry

ML Workbench collects anonymous usage data to help improve the extension. We take your privacy seriously.

### What Data is Collected

We collect analytics to understand feature usage and identify areas for improvement:

- **Feature usage**: Which features are used (file opens, view switches, tokenizer selection)
- **Performance metrics**: Load times, file size categories (small/medium/large), row count categories
- **Error patterns**: Error types and sanitized error messages (no file paths or user data)
- **Format popularity**: Which file formats are opened (JSONL, JSON, CSV, Parquet, Arrow)
- **Tokenizer usage**: Which tokenizers and modes are selected
- **Session information**: Extension version, VS Code version, platform (Windows/Mac/Linux)

### What is NOT Collected (Privacy Protected)

We never collect personally identifiable information (PII):

- ❌ **No file paths, names, or contents**
- ❌ **No search terms** (only categorized length: short/medium/long)
- ❌ **No actual token counts** (only success/failure and timing)
- ❌ **No user data from your files**
- ❌ **No email addresses, usernames, or credentials**

All error messages are automatically sanitized to remove file paths, emails, tokens, and other sensitive data before transmission.

### How to Disable Telemetry

Telemetry respects your VS Code global telemetry settings:

1. Open VS Code Settings (`Cmd/Ctrl + ,`)
2. Search for "telemetry"
3. Set **Telemetry Level** to `off`

When disabled, no data is collected or sent.

### Technical Details

- Uses [Azure Application Insights](https://docs.microsoft.com/en-us/azure/azure-monitor/app/app-insights-overview) for analytics
- GDPR compliant with automatic PII sanitization
- All telemetry code is open source in this repository

### Developer Setup (Telemetry)

To enable telemetry during development:

1. Create an Application Insights resource in Azure Portal
2. Copy the connection string from the resource
3. Set the environment variable:
   ```bash
   # macOS/Linux
   export APP_INSIGHTS_KEY="your-connection-string"

   # Windows (PowerShell)
   $env:APP_INSIGHTS_KEY="your-connection-string"
   ```
4. Restart VS Code to pick up the environment variable

For production deployments, set the `APP_INSIGHTS_KEY` environment variable in your deployment environment or use GitHub Secrets for CI/CD pipelines.

## License

MIT

**Note on Bundled Tokenizers**: This extension includes tokenizer files from various HuggingFace models for offline token counting. Each tokenizer retains its original license from the source model. See `/tokenizers/MANIFEST.md` for details.
