# ML Workbench

VS Code extension for viewing JSONL datasets with accurate token counting for ML training data.

## Features

### JSONL Viewer
- Open `.jsonl` files with formatted display (card, table, or raw views)
- Accurate token counting using real model tokenizers (16 models supported)
- Automatic chat template application for training data
- Handles files of any size with streaming (tested with 100GB+ files)
- Search and filter records
- Jump to specific line numbers
- Multiple tokenization modes (auto, chat, full JSON, specific key, raw text)

## Installation

```bash
npm install
npm run compile
```

Press F5 to launch in Extension Development Host.

## Usage

1. Open any `.jsonl` file
2. Switch between views: Cards (default), Table, or Raw
3. Select tokenizer from dropdown for accurate token counts
4. Choose tokenization mode (auto, chat, full JSON, key, raw text)
5. Use search to filter records

## Supported Tokenizers

**16 model families with bundled tokenizers (100% offline):**

- **Qwen**: 3.x, 2.5
- **DeepSeek**: V3/R1
- **Llama**: 3.x
- **Gemma**: 3.x, 2.x
- **Mistral**: Tekken, V3, V1
- **Phi**: 4.x
- **Command R**: Family
- **GPT**: 5.x/gpt-oss, 4o, 4, 2
- **Claude**: 3.x/4.x

All tokenizers include native chat templates for accurate training data token counts.

## Requirements

- VS Code 1.85.0+

## Development

```bash
npm run watch   # Auto-compile on changes
npm run package # Create .vsix
```

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
