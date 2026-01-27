# ML Workbench

VS Code extension for viewing JSONL datasets and chatting with local models.

## Features

### JSONL Viewer
- Open `.jsonl` files with formatted display (card, table, or raw views)
- Token counting with multiple tokenizer support (GPT-4, Claude, Llama, Qwen, etc.)
- Handles files of any size with streaming (tested with 100GB+ files)
- Search and filter records
- Jump to specific line numbers

### Model Chat
- Double-click `.gguf` files to chat instantly
- Automatic Ollama integration (installs if needed)
- Streaming responses
- Automatic model cleanup

## Installation

```bash
npm install
npm run compile
```

Press F5 to launch in Extension Development Host.

## Usage

### JSONL Viewer
1. Open any `.jsonl` file
2. Switch between views: Cards (default), Table, or Raw
3. Select tokenizer from dropdown for accurate token counts
4. Use search to filter records

### Model Chat
1. Double-click a `.gguf` file
2. If prompted, install Ollama
3. Start chatting

## Tokenizer Support

**Exact tokenizers:** GPT-4, GPT-3.5, GPT-3, GPT-2, Claude

**With chat templates (~90-95% accurate):** Llama 3, Llama 2, Mistral, Qwen, ChatGLM

**Approximations (~85-92% accurate):** Qwen 2.5, Baichuan, Yi, Gemma, Phi, DeepSeek, InternLM

For chat completions format (`{"messages": [...]}`), the appropriate chat template is automatically applied before tokenization.

## Requirements

- VS Code 1.85.0+
- For Model Chat: Ollama (auto-installed on Mac/Linux)

## Development

```bash
npm run watch   # Auto-compile on changes
npm run package # Create .vsix
```

## License

MIT
