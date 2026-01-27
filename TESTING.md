# Testing Guide

## Quick Start

```bash
npm install
npm run compile
# Press F5 in VS Code
```

## Test 1: JSONL Viewer

**File:** `PromptBridge-0.6b-Alpha/test-data.jsonl`

1. Click on `test-data.jsonl`
2. Verify JSONL viewer opens (not text editor)
3. Check:
   - Records show as formatted cards
   - JSON is syntax-highlighted
   - Token counts appear
   - Table view works (click "📊 Table")
   - Raw view works (click "📄 Raw")
   - Search filters records
   - Tokenizer dropdown changes token counts

## Test 2: Large File Performance

Generate a test file:
```bash
cd PromptBridge-0.6b-Alpha
python3 -c "
import json
for i in range(10000):
    print(json.dumps({'id': i, 'text': f'Record {i}', 'data': list(range(50))}))
" > large-test.jsonl
```

1. Open `large-test.jsonl`
2. Should load in < 3 seconds
3. Memory should stay under 200MB
4. Try "Load More" button
5. Try "Jump to line"

## Test 3: Model Chat (Optional)

Requires a GGUF model file.

Quick test model:
```bash
curl -L -o tinyllama.gguf \
  "https://huggingface.co/TheBloke/TinyLlama-1.1B-Chat-v1.0-GGUF/resolve/main/tinyllama-1.1b-chat-v1.0.Q4_K_M.gguf"
```

1. Double-click `tinyllama.gguf`
2. If prompted, click "Install Ollama"
3. Wait for model to load
4. Type a message and press Enter
5. Verify response streams in
6. Close tab (model should auto-cleanup)

## Expected Results

✅ JSONL files open in custom viewer  
✅ Token counts accurate for selected tokenizer  
✅ Large files don't crash or hang  
✅ Table header appears at top (not after first row)  
✅ Line numbering starts at 0  
✅ Model chat streams responses  

## Common Issues

**JSONL viewer doesn't open:** Right-click file → "Open With" → "JSONL Viewer"

**Token counts wrong:** Check tokenizer selection matches your target model

**Model chat fails:** Verify Ollama is running: `curl http://localhost:11434/api/tags`

## Performance Benchmarks

| File Size | Lines | Expected Load | Memory |
|-----------|-------|--------------|--------|
| < 1MB | < 1K | < 1s | < 50MB |
| 10-100MB | 10K-100K | 1-3s | 50-200MB |
| 100MB-1GB | 100K-1M | 3-10s | 100-500MB |
| > 1GB | > 1M | 10-30s | 200-800MB |
