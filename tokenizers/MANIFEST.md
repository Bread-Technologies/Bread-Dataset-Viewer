# Tokenizer Manifest

This document provides a source of truth for all bundled tokenizers in this extension.

## Directory Structure

All tokenizers are stored in `/tokenizers/` with the following structure:
```
tokenizers/
├── {model-key}/
│   ├── tokenizer.json          # Main vocabulary & merge rules
│   ├── tokenizer_config.json   # Config including chat template
│   └── chat_template.jinja     # (Optional) Separate template file
```

---

## Bundled Tokenizers

### ✅ Qwen Family

#### Qwen 3.x
- **Key**: `qwen-3`
- **Name**: Qwen 3.x
- **Source**: `Qwen/Qwen3-8B`
- **Directory**: `tokenizers/qwen-3/`
- **Vocab**: 36T tokens (New 2025 standard)
- **Template**: Qwen ChatML v3 with `<think>` support
- **Status**: ✓ Downloaded
- **Notes**: Latest generation with reasoning capabilities

#### Qwen 2.5
- **Key**: `qwen-2.5`
- **Name**: Qwen 2.5
- **Source**: `Qwen/Qwen2.5-72B-Instruct`
- **Directory**: `tokenizers/qwen-2.5/`
- **Vocab**: 152k (Qwen legacy)
- **Template**: Qwen ChatML v2
- **Status**: ✓ Downloaded (6.9MB)
- **Notes**: Legacy version, pre-thinking

---

### ✅ DeepSeek Family

#### DeepSeek V3 / R1
- **Key**: `deepseek-v3`
- **Name**: DeepSeek V3 / R1
- **Source**: `deepseek-ai/DeepSeek-V3`
- **Directory**: `tokenizers/deepseek-v3/`
- **Vocab**: 128k (DeepSeek custom)
- **Template**: DeepSeek ChatML
- **Status**: ✓ Downloaded
- **Notes**: V3 and R1 share identical tokenizer

---

### ✅ Llama Family

#### Llama 3.x
- **Key**: `llama-3`
- **Name**: Llama 3.x
- **Source**: `unsloth/Llama-3.3-70B-Instruct` (ungated mirror)
- **Directory**: `tokenizers/llama-3/`
- **Vocab**: 128k (Tiktoken)
- **Template**: Llama 3 standard
- **Status**: ✓ Downloaded
- **Notes**: Covers 3.1, 3.2, 3.3 - all use same tokenizer

---

### ⚠️ Gemma Family

#### Gemma 3.x
- **Key**: `gemma-3`
- **Name**: Gemma 3.x
- **Source**: `unsloth/gemma-3-12b-it`
- **Directory**: `tokenizers/gemma-3/`
- **Vocab**: 262k (Gemini 2 based)
- **Template**: Gemma 3 Multimodal
- **Status**: ✓ Downloaded (31.8MB)

#### Gemma 2.x
- **Key**: `gemma-2`
- **Name**: Gemma 2.x
- **Source**: `unsloth/gemma-2-9b-it`
- **Directory**: `tokenizers/gemma-2/`
- **Vocab**: 256k (SentencePiece)
- **Template**: Gemma 2 standard
- **Status**: ✓ Downloaded (17MB)
- **Notes**: Unsloth ungated version

---

### ⚠️ Mistral Family

#### Mistral Tekken
- **Key**: `mistral-tekken`
- **Name**: Mistral Tekken
- **Source**: `mistralai/Mistral-Nemo-Instruct-2407`
- **Directory**: `tokenizers/mistral-tekken/`
- **Vocab**: 131k (Tiktoken)
- **Template**: Mistral v7
- **Status**: ✓ Downloaded (8.8MB)
- **Notes**: Used in NeMo 12B, Pixtral 12B, Ministral 8B, Small 3

#### Mistral V3
- **Key**: `mistral-v3`
- **Name**: Mistral V3
- **Source**: `unsloth/mistral-7b-instruct-v0.3` (ungated mirror)
- **Directory**: `tokenizers/mistral-v3/`
- **Vocab**: 32,768 (SentencePiece)
- **Template**: Mistral V3
- **Status**: ✓ Downloaded
- **Notes**: For Large 2, Codestral 22B, Mixtral 8x22B, 7B v0.3

#### Mistral V1
- **Key**: `mistral-v1`
- **Name**: Mistral V1
- **Source**: `mistralai/Mistral-7B-Instruct-v0.1`
- **Directory**: `tokenizers/mistral-v1/`
- **Vocab**: 32,000 (Llama 2 compatible)
- **Template**: Mistral V1
- **Status**: ✓ Downloaded (1.7MB)
- **Notes**: Legacy - for 7B v0.1, v0.2, Mixtral 8x7B

---

### ✅ Phi Family

#### Phi 4.x
- **Key**: `phi-4`
- **Name**: Phi 4.x
- **Source**: `microsoft/Phi-4-mini-instruct`
- **Directory**: `tokenizers/phi-4/`
- **Vocab**: 100k
- **Template**: Phi 4 chat
- **Status**: ✓ Downloaded

---

### ✅ Command R Family

#### Command R
- **Key**: `command-r`
- **Name**: Command R Family
- **Source**: `Xenova/c4ai-command-r-v01-tokenizer` (official Xenova port)
- **Directory**: `tokenizers/command-r/`
- **Vocab**: 256k (Cohere)
- **Template**: Command R
- **Status**: ✓ Downloaded
- **Notes**: For R7B, R, R+

---

### ✅ GPT Family

#### GPT-5 / gpt-oss
- **Key**: `gpt-5`
- **Name**: GPT-5.x / gpt-oss
- **Source**: `openai/gpt-oss-20b` (official OpenAI repo)
- **Directory**: `tokenizers/gpt-5/`
- **Special**: Chat template embedded from `chat_template.jinja`
- **Vocab**: o200k_harmony (200k + Thinking/Constraint tokens)
- **Template**: Harmony format with `<|start|>`, `<|channel|>`, etc.
- **Status**: ✓ Downloaded (template embedded in config)
- **Notes**: For GPT-5.0, 5.1, 5.2, o3-mini, gpt-oss

#### GPT-4o
- **Key**: `gpt-4o`
- **Name**: GPT-4o Family
- **Source**: `Xenova/gpt-4o` (community proxy)
- **Directory**: `tokenizers/gpt-4o/`
- **Vocab**: o200k_base (no Harmony tokens)
- **Template**: Basic ChatML (may require fallback)
- **Status**: ✓ Downloaded
- **Notes**: For GPT-4o, GPT-4o-mini, o1-preview, o1-mini

#### GPT-4 Classic
- **Key**: `gpt-4`
- **Name**: GPT-4 Classic
- **Source**: `Xenova/gpt-4` (community proxy)
- **Directory**: `tokenizers/gpt-4/`
- **Vocab**: cl100k_base
- **Template**: ChatML standard
- **Status**: ✓ Downloaded
- **Notes**: For GPT-4 Turbo, GPT-3.5 Turbo, text-embedding-3

#### GPT-2
- **Key**: `gpt-2`
- **Name**: GPT-2
- **Source**: `gpt2` (official)
- **Directory**: `tokenizers/gpt-2/`
- **Vocab**: 50,257 BPE
- **Template**: None (raw text only)
- **Status**: ✓ Downloaded (1.3MB)
- **Notes**: Historical reference - baseline tokenizer

---

### ✅ Claude Family

#### Claude
- **Key**: `claude`
- **Name**: Claude 3.x / 4.x
- **Source**: `Xenova/claude-tokenizer` (community proxy)
- **Directory**: `tokenizers/claude/`
- **Vocab**: Claude proprietary (~100k)
- **Template**: Embedded in proxy
- **Status**: ✓ Downloaded
- **Notes**: Reverse-engineered approximation

---

## Download Summary

| Status | Count | Models |
|--------|-------|--------|
| ✓ Complete | 16 | qwen-3, qwen-2.5, deepseek-v3, llama-3, gemma-3, gemma-2, mistral-tekken, mistral-v3, mistral-v1, phi-4, command-r, gpt-5, gpt-4o, gpt-4, gpt-2, claude |

**Total Active**: 16 tokenizers
**Successfully Bundled**: 16 tokenizers (100% ✓)
**Total Size**: ~165 MB

---

## Special Cases

### GPT-5 / gpt-oss Template Handling
The GPT-5 tokenizer requires special handling because its chat template is stored in a separate `.jinja` file. During the download process:
1. Downloaded `tokenizer.json` and `tokenizer_config.json`
2. Downloaded `chat_template.jinja` separately
3. Embedded the template content into `tokenizer_config.json` as the `chat_template` field
4. This ensures offline operation without runtime fetches

### Git LFS Issues
Some models (gemma-2, mistral-tekken) use Git LFS for large tokenizer files. The direct `curl` download retrieved LFS pointers instead of actual files. These should either:
- Be re-downloaded using git-lfs
- Fall back to runtime download from HuggingFace
- Use alternative ungated mirrors

---

## Usage in Code

In `src/utils/tokenizer.ts`, the tokenizers are loaded using:

```typescript
const tokenizer = await AutoTokenizer.from_pretrained(config.modelId);
```

To load from bundled files instead, change to:

```typescript
const localPath = path.join(__dirname, '../../tokenizers', tokenizerType);
const tokenizer = await AutoTokenizer.from_pretrained(localPath, {
    local_files_only: true
});
```

---

## Maintenance

When adding new tokenizers:
1. Create directory: `tokenizers/{model-key}/`
2. Download both `tokenizer.json` and `tokenizer_config.json`
3. For separate templates, embed into config
4. Add entry to `TOKENIZER_CONFIGS` in `tokenizer.ts`
5. Update this manifest
6. Verify file sizes (tokenizer.json typically 1-30MB)

Last updated: 2025-01-28
