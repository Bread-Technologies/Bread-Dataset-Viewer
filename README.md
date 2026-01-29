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

## License

MIT
