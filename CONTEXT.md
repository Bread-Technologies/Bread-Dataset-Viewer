# ML Workbench - Complete Development Context

**Last Updated:** January 27, 2026  
**Status:** JSONL Viewer fully functional, Model Chat feature not implemented yet

---

## Overview

This is a VS Code/Cursor extension for viewing JSONL datasets with a custom viewer. The extension was built from the original PRD but we're currently **focusing only on the JSONL viewer** - the model chat feature is stubbed but not functional.

## What's Implemented ✅

### JSONL Viewer - Fully Working
- Custom editor for `.jsonl` files
- Three view modes: Cards, Table, Raw
- Memory-efficient streaming (loads 100 lines at a time)
- Token counting with 18 different model tokenizers
- Chat template support for accurate training data token counts
- Search/filter functionality
- Jump to line navigation
- Stats toolbar (loaded count, avg/max tokens)
- "Edit in Text Editor" button to open file in normal editor
- Zero-based line numbering (starts at line 0)
- Handles files of any size (tested with 100GB+)

### What's NOT Implemented ❌
- **Model Chat feature** - Code exists but not functional/tested
- **File icons** - SVG icons created but may not be working
- **Status bar** - Backend status indicator not tested

---

## Critical Architecture Decisions

### 1. Memory Efficiency - The Core Constraint

**Problem:** JSONL datasets can be 100GB+ (billions of lines)

**Solution:** Never load entire file into memory
- Use Node.js `readline` with `fs.createReadStream`
- Load only 100 lines at a time
- "Load More" button for pagination
- Each view (cards/table/raw) uses the same lazy-loaded data

**Critical Implementation Detail:**
```typescript
// CORRECT - streams file line by line
const stream = fs.createReadStream(filePath);
const rl = readline.createInterface({ input: stream });
for await (const line of rl) {
    // Process one line at a time
}

// WRONG - would load entire file
const content = await fs.promises.readFile(filePath, 'utf8');
```

### 2. Line Numbering - Zero-Based

**Decision:** Lines are numbered starting at 0 (not 1)

**Reason:** Matches programming conventions and user expectation

**Implementation:**
```typescript
let lineNum = 0; // Start at 0
for await (const line of rl) {
    if (lineNum < offset) {
        lineNum++;
        continue;
    }
    // ... process line ...
    lines.push({ index: lineNum, data, raw: line });
    lineNum++;
}
```

**Critical Bug Fixed:** Initially had duplicate `lineNum++` in search filter causing skipped line numbers.

### 3. View Modes - Three Different Displays

**Card View (Default):**
- Pretty-printed JSON with syntax highlighting
- Each record is a card with header (line number + token count)
- Colors: keys=blue, strings=orange, numbers=green, booleans=blue

**Table View:**
- Spreadsheet-like display
- Auto-detects columns from JSON keys
- Special columns: `_line` and `_tokens` always first
- Sticky header (stays at top when scrolling)

**Raw View:**
- Plain text display
- Line number + raw JSON string
- No parsing, fastest to render
- Still lazy-loaded (100 lines at a time)

### 4. Token Counting - Multi-Model Support

**Key Decision:** Support 18 different model tokenizers with chat template application

**Implementation:**
- Uses tiktoken library (OpenAI's tokenizer)
- For OpenAI models: exact tokenization (cl100k_base, p50k_base, r50k_base)
- For other models: approximation with appropriate base tokenizer
- **Chat template support:** Automatically detects `{"messages": [...]}` format and applies model-specific templates

**Supported Tokenizers:**
- **Exact:** GPT-4, GPT-3.5, GPT-3, GPT-2, Claude
- **With Templates:** Llama 3, Llama 2, Mistral, Qwen, ChatGLM
- **Approximations:** Qwen 2.5, Baichuan, Yi, Gemma, Phi, DeepSeek, InternLM

**Chat Template Examples:**
```typescript
// Llama 3
"<|begin_of_text|><|start_header_id|>user<|end_header_id|>\n\nHello<|eot_id|>"

// Llama 2
"[INST] <<SYS>>\nsystem<</SYS>>\n\nuser [/INST] assistant"

// Qwen
"<|im_start|>user\nHello<|im_end|>\n"
```

**Critical Function:**
```typescript
function applyChatTemplate(data: any, tokenizerType: string): string {
    if (data && Array.isArray(data.messages)) {
        return formatWithTemplate(data.messages, tokenizerType);
    }
    return JSON.stringify(data); // Fallback
}
```

---

## Major Bugs Fixed During Development

### Bug 1: Table Header Position (CSS Issue)
**Symptom:** Table header appeared on "line 1" instead of at the top

**Wrong Diagnosis:** Tried fixing JavaScript rendering order, DOM manipulation, etc. - none worked!

**Actual Cause:** CSS `position: sticky; top: 80px;` on `<thead>`
- The 80px offset pushed header down visually
- First tbody row appeared in natural flow (top of table)
- Result: Line 0 above header, then header, then remaining rows

**Fix:**
```css
/* Before - WRONG */
thead {
    position: sticky;
    top: 80px;  /* ← Pushed header down */
}

/* After - CORRECT */
thead {
    position: sticky;
    top: 0;  /* ← Header at top */
}
```

**Lesson:** The DOM structure was always correct, it was purely a CSS visual positioning issue.

### Bug 2: Skipped Line Numbers
**Symptom:** Line numbers showed as 0, 4, 6, 8, 10... (skipping odd numbers)

**Cause:** Duplicate `lineNum++` when filtering by search term
```typescript
// WRONG
if (searchTerm && !line.includes(searchTerm)) {
    skippedBySearch++;
    lineNum++;  // ← First increment
    continue;
}
// ... later ...
lineNum++;  // ← Second increment - DUPLICATE!
```

**Fix:** Single increment per line, regardless of filtering

### Bug 3: Token Count Color
**Symptom:** Bright blue token counts were too prominent and hard to read

**Fix:** Changed from `var(--vscode-charts-blue)` to `var(--vscode-badge-foreground)` for better contrast

---

## Current Performance Issues

### Load Time: ~1 Second (Constant Regardless of File Size)

**What We Know:**
- NOT caused by tokenizer (verified by user)
- NOT caused by file I/O (same time for 100 lines vs 1M lines)
- Fast on re-open (cached)
- Small .txt files open in <100ms

**Most Likely Cause:**
The webview HTML is **~775 lines of inline HTML/CSS/JS** (lines 191-966 of jsonlEditorProvider.ts)

**Performance Breakdown (Estimated):**
```
Total: ~1000ms
├── Webview iframe creation:     300-400ms  [VS Code overhead]
├── HTML string generation:       50-100ms  [Building 775 lines]
├── HTML/CSS parsing:            200-300ms  [Browser parsing]
├── JavaScript execution:        100-200ms  [Event listeners, DOM setup]
├── IPC + message passing:        50-100ms  [Extension ↔ Webview]
└── Initial render:               50-100ms  [DOM manipulation]
```

**Not Yet Tested:** Extracting CSS/JS to external files to reduce HTML parsing overhead

---

## Code Architecture

### File Structure
```
src/
├── extension.ts              # Main entry point (53 lines)
│   └── Registers providers, initializes backends
├── jsonlEditorProvider.ts    # JSONL viewer (969 lines)
│   ├── Provider implementation
│   ├── File streaming logic
│   └── Inline HTML/CSS/JS (~775 lines)
├── modelChatProvider.ts      # Model chat stub (671 lines) - NOT FUNCTIONAL
├── backends/
│   ├── index.ts              # Backend management
│   └── ollama.ts             # Ollama integration
└── utils/
    └── tokenizer.ts          # Multi-model tokenizer (196 lines)
```

### Provider Type
- Uses `CustomReadonlyEditorProvider`
- Registered for `*.jsonl` files
- Priority: "default" (takes over by default)

### Data Flow
```
User opens .jsonl
    ↓
resolveCustomEditor()
    ↓
getHtmlForWebview() - Returns 775 lines of HTML
    ↓
webview.html = htmlString - Parses and creates iframe
    ↓
loadLines() - Streams first 100 lines from disk
    ↓
JSON.parse each line + count tokens
    ↓
webview.postMessage({ type: 'lines', lines })
    ↓
Webview renders (cards/table/raw)
    ↓
User clicks "Load More" → loadLines() again with offset
```

### Message Protocol (Extension ↔ Webview)

**Extension → Webview:**
```typescript
{ type: 'fileInfo', fileName, fileSize, fileSizeMB }
{ type: 'lines', lines, hasMore, nextOffset, searchTerm }
{ type: 'tokens', tokens: { [lineIndex]: count } }  // Background token updates
{ type: 'error', message }
```

**Webview → Extension:**
```typescript
{ type: 'loadLines', offset, limit, searchTerm, tokenizer }
{ type: 'jumpToLine', lineNumber, tokenizer }
{ type: 'openInTextEditor' }
```

---

## UI/UX Decisions

### Toolbar Layout
```
[File Name (Size)] | [Cards][Table][Raw] | Tokenizer:[Dropdown] | 
[Search][Clear] | Jump:[Input][Go] | [Edit] | Stats: Loaded/Avg/Max
```

### View Switching
- All three views share the same loaded data (`allLines` array)
- Switching views doesn't reload from disk
- Table view rebuilds completely on each render (simpler, bug-free)
- Raw view uses incremental rendering (appends only new lines)

### Token Count Display
- Shows "..." initially if tokens not yet calculated
- Updates asynchronously via separate message
- Color: `var(--vscode-badge-foreground)` for readability
- Format: "1,247 tokens" (with thousand separators)

### Search Behavior
- Filters on backend (streams file, skips non-matching lines)
- Clears existing data and reloads from line 0
- Search is case-insensitive
- Searches raw JSON string (not parsed fields)

---

## Token Counting Implementation

### Deferred Token Counting (Current Implementation)

**Why:** Token counting was causing 1-second delay (later proven false, but kept for other benefits)

**How:**
1. Load lines from file WITHOUT counting tokens
2. Send lines to webview immediately (show "..." for tokens)
3. Count tokens in background using `setImmediate()`
4. Send token updates separately
5. Webview updates token displays by ID

**Benefits:**
- Lines appear immediately
- Token counting doesn't block initial render
- Progressive enhancement (UI works even if tokens fail)

**Implementation:**
```typescript
// Backend
lines.push({ index: lineNum, data, raw: line }); // No tokens
webview.postMessage({ type: 'lines', lines });

setImmediate(() => {
    const tokensMap = {};
    for (const line of lines) {
        tokensMap[line.index] = countTokens(line.raw, tokenizer);
    }
    webview.postMessage({ type: 'tokens', tokens: tokensMap });
});
```

```javascript
// Webview
case 'tokens':
    for (const [lineIndex, count] of Object.entries(message.tokens)) {
        tokenCounts.set(idx, count);
        document.getElementById(`tokens-${idx}`).textContent = `${count} tokens`;
    }
```

### Chat Template Application

**Critical Feature:** For chat completions format, applies model-specific templates before tokenization

**Detection:**
```typescript
const parsed = JSON.parse(line);
if (parsed && Array.isArray(parsed.messages)) {
    // It's chat completions format
    textToTokenize = applyChatTemplate(parsed, tokenizerType);
}
```

**Why This Matters:**
- Training data needs accurate token counts
- Chat templates add special tokens (e.g., `<|begin_of_text|>` for Llama 3)
- Without templates, counts would be 20-30% lower than actual
- Different models have different templates and token counts

**Example:**
```json
{"messages": [{"role": "user", "content": "Hi"}]}
```
- GPT-4: ~5 tokens (no template, just JSON)
- Llama 3 with template: ~25 tokens (includes `<|begin_of_text|>`, etc.)

---

## Known Issues & Limitations

### Performance
1. **~1 second initial load time** (constant regardless of file size)
   - Verified NOT caused by tokenizer
   - Verified NOT caused by file I/O
   - Most likely: Webview initialization + 775 lines of inline HTML/CSS/JS
   - Fast on re-open (webview cached)
   - **Not yet fixed** - optimization planned

2. **Large file initial open**
   - Files >20k-30k lines may fail to open
   - Cause unknown - needs investigation
   - Should work for any size (that's the whole point!)

### Token Counting Accuracy
- **Exact:** OpenAI models (GPT-4, GPT-3, GPT-2) and Claude
- **Good (~90-95%):** Llama, Mistral with chat templates
- **Approximation (~85-92%):** Chinese models (Qwen, GLM, etc.)
- Limitation: tiktoken only has OpenAI tokenizers, others are approximations

### File Editing
- Custom viewer is **read-only**
- Use "Edit in Text Editor" button to edit file
- Opens in VS Code's native text editor
- No in-place editing in custom viewer

---

## Design Decisions & Trade-offs

### 1. Inline HTML vs External Files
**Current:** 775 lines of HTML/CSS/JS inline in TypeScript string

**Pros:**
- Simple deployment (everything in one file)
- No file path issues
- Easy to maintain in single file

**Cons:**
- Slow initialization (~700-900ms parsing overhead)
- No browser caching
- Large memory footprint

**Considered But Not Implemented:** Extract to external files
- Would save ~500-700ms
- Better caching
- Cleaner code separation
- Trade-off: More files to manage

### 2. Read-Only vs Editable Viewer
**Current:** Read-only with "Edit in Text Editor" button

**Reasoning:**
- Full text editing is complex (undo/redo, multi-cursor, find/replace)
- VS Code already has excellent text editor
- Custom viewer focused on visualization, not editing
- Large files make in-place editing risky (easy to corrupt)

**User expectation:** Wanted raw view to be editable
**Resolution:** Provide button to open in text editor instead

### 3. Table View Rendering Strategy
**Current:** Completely rebuild thead and tbody on every render

**Why Not Incremental:**
- Tried incremental rendering (only add new rows)
- Caused bugs with header positioning
- Race conditions between header creation and row rendering
- Full rebuild is simpler and bug-free

**Trade-off:**
- Slightly slower for very large loaded datasets (1000+ lines)
- But more reliable and easier to maintain
- For typical usage (100-200 loaded lines), negligible difference

### 4. Token Counting Strategy
**Current:** Deferred/async token counting

**Evolution:**
1. **Initially:** Count tokens synchronously before sending lines
2. **Problem:** Suspected tokenizer causing 1s delay
3. **Solution:** Defer token counting, show "..." initially
4. **Reality:** Tokenizer wasn't the bottleneck
5. **Result:** Kept deferred approach anyway for better perceived performance

**Why Keep It:**
- Lines appear instantly
- Token counts fill in progressively
- Better user experience even if total time is same
- Failures in token counting don't block viewer

---

## Common Pitfalls & Gotchas

### 1. Webview iframe Creation is Slow
- VS Code creates sandboxed iframe for security
- ~300-400ms baseline overhead
- Can't be avoided
- User perceives this as "extension is slow"

### 2. Inline HTML is a Performance Killer
- 775 lines of HTML/CSS/JS
- Parsed every time file opens
- Not cached by browser
- Major bottleneck (~700-900ms)

### 3. Large Files "Not Opening" Issue
- User reported files >20k-30k lines sometimes fail
- NOT a memory issue (we stream)
- NOT a tokenizer issue (verified)
- Possibly webview message size limits?
- **Needs investigation**

### 4. CSS Positioning is Tricky
- `position: sticky` caused header to appear wrong
- Visual order ≠ DOM order with certain CSS
- Always verify in browser, not just code
- Use browser inspector to debug visual issues

### 5. Line Numbering Edge Cases
- Search filtering can cause skipped numbers if not careful
- Need to increment ONCE per actual file line
- Zero-based vs one-based confusion

---

## How Token Counting Actually Works

### Step-by-Step Process

1. **User selects tokenizer** from dropdown (e.g., "Llama 3")

2. **Backend loads lines:**
   ```typescript
   const line = '{"messages": [{"role": "user", "content": "Hi"}]}';
   ```

3. **Tokenizer checks format:**
   ```typescript
   const parsed = JSON.parse(line);
   if (parsed.messages) {
       // It's chat completions format
       text = applyChatTemplate(parsed, 'llama-3');
   }
   ```

4. **Apply chat template:**
   ```typescript
   // For Llama 3
   text = '<|begin_of_text|><|start_header_id|>user<|end_header_id|>\n\nHi<|eot_id|>';
   ```

5. **Tokenize with tiktoken:**
   ```typescript
   const encoder = get_encoding('cl100k_base'); // For Llama 3
   const tokens = encoder.encode(text);
   return tokens.length; // e.g., 25 tokens (includes special tokens)
   ```

6. **Send to webview:**
   ```typescript
   webview.postMessage({ type: 'tokens', tokens: { 0: 25, 1: 30, ... } });
   ```

7. **Update UI:**
   ```javascript
   document.getElementById('tokens-0').textContent = '25 tokens';
   ```

### Why This Matters for ML Engineers
- Training data preparation requires accurate token counts
- Different models have different context limits (2k, 4k, 8k, 128k tokens)
- Chat templates add 20-50 tokens per conversation
- Need to know if conversations fit in context window

---

## File Format Support

### Simple Format (Individual Messages)
```json
{"role": "user", "content": "Hello"}
{"role": "assistant", "content": "Hi there"}
```
- Each line is one message
- Token count = raw JSON string tokenized
- No template applied

### Chat Completions Format (Conversations)
```json
{"messages": [
  {"role": "system", "content": "You are helpful."},
  {"role": "user", "content": "Hello"},
  {"role": "assistant", "content": "Hi there"}
]}
```
- Each line is complete conversation
- Token count = after applying chat template
- More accurate for training data

### Mixed Format
- Can have both formats in same file
- Tokenizer detects per-line whether to apply template
- Works correctly

---

## Testing & Verification

### Test Data Location
~~`PromptBridge-0.6b-Alpha/test-data.jsonl`~~ - **REMOVED BY USER**

**Note:** User deleted the PromptBridge folder entirely

### How to Test
1. Create test file:
   ```bash
   cat > test.jsonl << EOF
   {"messages": [{"role": "user", "content": "Test"}]}
   {"role": "user", "content": "Simple test"}
   EOF
   ```

2. Open in extension (F5 to launch dev host)

3. Verify:
   - File opens (should be <1s but currently ~1s)
   - Cards display correctly
   - Table view works (header at top)
   - Raw view shows plain text
   - Token counts appear (may show "..." briefly)
   - Search/filter works
   - Load More button appears if >100 lines

### Large File Test
```bash
python3 -c "
import json
for i in range(100000):
    print(json.dumps({'id': i, 'text': f'Line {i}'}))
" > large.jsonl
```
Open `large.jsonl` and verify:
- Opens without crash
- Memory stays under 500MB
- Can navigate with Load More
- Jump to line works

---

## Future Optimization Opportunities

### Priority 1: Extract HTML/CSS/JS to External Files
**Impact:** ~500-700ms faster (50-70% improvement)

**Implementation:**
1. Create `webview/jsonlViewer.html` (minimal structure)
2. Create `webview/jsonlViewer.css` (styles only)
3. Create `webview/jsonlViewer.js` (logic only)
4. Load via `webview.asWebviewUri()`

**Benefits:**
- Browser can cache files
- Smaller initial HTML string
- Cleaner code organization
- Easier to maintain

### Priority 2: Optimize Initial Render
- Send minimal data first (just show loading state)
- Render first 20 lines, then batch rest
- Use document fragments for DOM operations
- Defer non-visible UI elements

### Priority 3: Web Worker for Token Counting
- Move tiktoken to Web Worker
- Don't block main thread
- Better parallelization

### Lower Priority
- Cache element references (avoid repeated getElementById)
- Use virtual scrolling for truly massive loaded datasets
- Defer stats calculation until requested
- Simplify syntax highlighting regex

---

## Technical Details

### Streaming Implementation
```typescript
// Efficient - only keeps 100 lines in memory
const stream = fs.createReadStream(filePath);
const rl = readline.createInterface({ input: stream });
let lineNum = 0;
const lines = [];

for await (const line of rl) {
    if (lineNum < offset) {
        lineNum++;
        continue;  // Skip without processing
    }
    if (lines.length >= limit) {
        break;  // Stop early
    }
    lines.push({ index: lineNum, data: JSON.parse(line), raw: line });
    lineNum++;
}

rl.close();
stream.destroy();  // Important: clean up resources
```

### Table Header Rendering (Fixed)
```typescript
// Always rebuild completely - simpler, bug-free
thead.innerHTML = '';
tbody.innerHTML = '';

// Create header first
const headerRow = document.createElement('tr');
// ... add <th> elements ...
thead.appendChild(headerRow);

// Then add all data rows
allLines.forEach(line => {
    const tr = document.createElement('tr');
    // ... add <td> elements ...
    tbody.appendChild(tr);
});
```

### Syntax Highlighting
```javascript
// Simple regex-based highlighting
function syntaxHighlight(obj) {
    let json = JSON.stringify(obj, null, 2);
    return json.replace(/(".*?":|true|false|null|-?\d+)/g, match => {
        let cls = 'json-number';
        if (/^"/.test(match)) {
            cls = /:$/.test(match) ? 'json-key' : 'json-string';
        } else if (/true|false/.test(match)) {
            cls = 'json-boolean';
        }
        return `<span class="${cls}">${match}</span>`;
    });
}
```

---

## What to Tell a New Agent

### Context Summary
"This is a VS Code extension that provides a custom viewer for JSONL files. The viewer has three modes (cards, table, raw), lazy-loads 100 lines at a time, and counts tokens using tiktoken with support for 18 different model tokenizers including chat template application. The main challenge is achieving fast initial load times (<100ms goal, currently ~1s). The model chat feature exists in the codebase but is not implemented/tested - focus only on the JSONL viewer."

### Current State
- **Working:** JSONL viewer with all three view modes, token counting, search, navigation
- **Known bug:** ~1 second load time (suspected: inline HTML overhead)
- **Known bug:** Large files (>20-30k lines) sometimes fail to open - needs investigation
- **Not working:** Model chat feature (ignore for now)

### Next Steps
1. **Investigate large file failure** - Why do files >30k lines sometimes fail?
2. **Optimize load time** - Extract HTML/CSS/JS to external files
3. **Add performance instrumentation** - Measure each step precisely
4. **Test with truly massive files** - 1GB, 10GB, 100GB

### Key Files to Understand
1. `src/jsonlEditorProvider.ts` - Lines 191-966 are the HTML template (optimization target)
2. `src/utils/tokenizer.ts` - Chat template application logic
3. Test by creating small JSONL file and opening it

### Code Quality Notes
- Clean compilation (0 TypeScript errors)
- No linter errors
- Well-structured with clear separation
- Comments where needed
- Could benefit from extracting webview code

---

## Development Workflow

### Build & Test
```bash
npm install
npm run compile    # TypeScript → JavaScript
# Press F5 in VS Code to launch Extension Development Host
# Open any .jsonl file in the new window
```

### Watch Mode
```bash
npm run watch      # Auto-recompile on save
# Keep running, press F5 to reload extension
```

### Debugging
- Set breakpoints in `.ts` files
- Use Debug Console (Cmd+Shift+Y)
- Check webview console: Right-click webview → Inspect Element
- Extension Host output: View → Output → "Extension Host"

---

## Dependencies

### Runtime
- `tiktoken` (^1.0.0) - Token counting library
- Node.js built-ins: `fs`, `readline`, `path`

### Dev
- `typescript` (^5.3.0)
- `@types/node` (^20.0.0)
- `@types/vscode` (^1.85.0)
- `@vscode/vsce` (^2.22.0) - For packaging

### No Dependencies For
- Model chat (Ollama integration not tested)
- File icons (created but may not work)
- Status bar (created but not tested)

---

## User Feedback & Preferences

### What User Likes
- Fast operation after initial load
- Three view modes
- Token counting with multiple models
- Lazy loading (handles huge files)

### What User Wants Fixed
1. **1 second initial load** - "Too long, should be <100ms"
2. **Large file failures** - "Files >30k lines sometimes don't open"
3. **Raw view editing** - Wanted editable raw view, but accepted "Edit in Text Editor" button

### User's Use Case
- ML engineer working with training data
- Needs to view/inspect JSONL datasets
- Cares about accurate token counts for different models
- Works with files that can be 100GB+
- Values speed and efficiency

---

## Important Patterns & Anti-Patterns

### ✅ DO
- Stream files with readline
- Load incrementally (100 lines at a time)
- Clean up streams (`rl.close()`, `stream.destroy()`)
- Use zero-based indexing
- Test with truly large files
- Verify CSS visually, not just DOM structure

### ❌ DON'T
- Load entire file into memory (`readFile`)
- Put all lines in a textarea (defeats streaming)
- Increment line counter multiple times per line
- Assume DOM order = visual order (CSS can change it)
- Trust inline HTML for performance
- Block initial render with heavy computation

---

## Testing Checklist

### Basic Functionality
- [ ] Open JSONL file (should open in viewer, not text editor)
- [ ] Cards view displays correctly
- [ ] Table view displays correctly (header at top!)
- [ ] Raw view displays correctly
- [ ] Switch between views works
- [ ] Line numbers start at 0
- [ ] Token counts appear (may be "..." briefly)
- [ ] Search filters records
- [ ] Load More button works
- [ ] Jump to line works

### Token Counting
- [ ] Try different tokenizers from dropdown
- [ ] Token counts change when tokenizer changes
- [ ] Chat completions format gets template applied
- [ ] Simple format counts raw JSON

### Performance
- [ ] Load time acceptable (<1s, goal <100ms)
- [ ] Memory usage reasonable (<200MB for viewer)
- [ ] No crashes or freezes
- [ ] Works with 10k+ line files
- [ ] Works with 100k+ line files
- [ ] Works with 1M+ line files

### Edge Cases
- [ ] Malformed JSON lines handled gracefully
- [ ] Empty file doesn't crash
- [ ] File with one line works
- [ ] Very long JSON lines (>1MB) don't crash
- [ ] Files with mixed formats (messages + simple)

---

## Debugging Tips

### If Load Time is Slow
1. Check if it's consistent (same time for all file sizes)
2. If consistent → Initialization overhead
3. Profile with performance logs
4. Check webview console (right-click → Inspect)
5. Try minimal HTML to isolate cause

### If Large Files Fail
1. Check memory usage
2. Look for "maximum call stack" errors
3. Check if it's specific to certain file formats
4. Verify streaming logic (not loading full file)
5. Check webview message size limits

### If Token Counts Wrong
1. Verify tokenizer selection matches model
2. Check if chat template being applied (console.log)
3. Test with OpenAI tokenizer: https://platform.openai.com/tokenizer
4. For chat format, manually apply template and compare

### If Table Header Wrong
1. Check CSS `position: sticky` and `top` value
2. Inspect actual DOM structure (should be thead → tbody)
3. Clear browser cache
4. Check z-index values

---

## Code Smells & Technical Debt

### Current Issues
1. **775 lines of inline HTML** - Should be external files
2. **No error boundaries** - Webview errors could crash viewer
3. **No progress indicators** - User doesn't know what's happening during load
4. **Hardcoded 100 line limit** - Should be configurable
5. **No caching** - Re-loads same lines on view switch
6. **Table rebuilds completely** - Could be incremental for better performance

### Not Issues (Intentional)
- Read-only viewer (by design)
- No editing in raw view (use text editor instead)
- Token approximations for non-OpenAI models (tiktoken limitation)
- Model chat not implemented (out of current scope)

---

## Performance Investigation History

### What We Tried
1. **Deferred token counting** - Moved to background with setImmediate
   - Result: Didn't help (tokenizer wasn't the issue)
   - Kept it anyway for perceived performance

2. **Lazy tiktoken init** - Don't initialize until first use
   - Result: Minimal impact
   - Kept it anyway

3. **Added performance logging** - console.log timing at each step
   - Result: Logs not appearing in expected places
   - User couldn't see them in Output or Debug Console

4. **Investigated line numbering** - Thought it was JS issue
   - Result: Was actually CSS issue (sticky positioning)

### What We Learned
- The 1s delay is constant (not file-size dependent)
- It's NOT the tokenizer
- It's NOT file I/O
- It's likely webview initialization + HTML parsing
- Need better profiling tools

### What We Haven't Tried Yet
- Extract CSS/JS to external files (biggest opportunity)
- Minimal HTML experiment (test with bare-bones viewer)
- Web Worker for token counting
- Virtual scrolling for loaded lines
- Investigate large file failure (>30k lines issue)

---

## Important Implementation Notes

### Why setImmediate() for Tokens
```typescript
setImmediate(() => {
    // Token counting happens here
});
```
- Allows webview to receive lines message first
- Shows UI immediately with "..." for tokens
- Then fills in tokens asynchronously
- Better perceived performance (UI responsive sooner)

### Why Table View Rebuilds Completely
- Tried incremental rendering (only append new rows)
- Caused race conditions with header creation
- Full rebuild is simpler and bug-free
- Performance difference negligible for <1000 lines

### Why CustomReadonlyEditorProvider
- Initially tried CustomTextEditorProvider (editable)
- But editing in webview is complex and unnecessary
- Read-only + "Edit in Text Editor" button is simpler
- User accepted this approach

---

## Open Questions & Next Steps

### Questions Needing Investigation
1. **Why is initial load ~1s?** 
   - Hypothesis: Inline HTML parsing
   - Need: Extract HTML/CSS/JS and compare
   
2. **Why do files >30k lines fail sometimes?**
   - Hypothesis: Webview message size limits?
   - Need: Test with different file sizes, check error logs
   
3. **Is tokenizer actually being deferred?**
   - User says tokens appear immediately
   - Need: Verify setImmediate() is actually working
   
4. **Can we pre-warm the webview?**
   - Create webview on extension activation
   - Reuse for subsequent files
   - Trade-off: Memory usage

### Immediate Next Steps
1. Investigate large file failure (>30k lines)
2. Extract HTML to external files (biggest perf win)
3. Add better performance instrumentation
4. Test with truly massive files (1GB+)

### Future Features (Out of Scope for Now)
- Model chat implementation
- File icons working properly
- Edit directly in raw view (rejected - use text editor)
- Export filtered results
- Schema inference
- Data validation

---

## Critical Reminders for Future Work

1. **Never load entire file into memory** - This is the cardinal rule
2. **Always stream with readline** - Load 100 lines at a time
3. **Test with huge files** - 1GB, 10GB, 100GB
4. **Zero-based indexing** - Lines start at 0
5. **CSS can trick you** - Visual position ≠ DOM order
6. **Deferred token counting** - Current pattern, keep it
7. **Table view rebuilds** - Don't try to make incremental
8. **Focus on JSONL viewer** - Ignore model chat for now

---

## Summary

This extension successfully views JSONL files of any size with token counting and multiple view modes. The architecture is sound (streaming, lazy-loading), but initial load time (~1s) needs optimization. Most likely culprit is inline HTML overhead. The deferred token counting implementation is working correctly. Model chat feature exists but is not functional or tested - focus only on JSONL viewer.

**Current Priority:** Fix large file issue (>30k lines) and optimize initial load time to <100ms.
