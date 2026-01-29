const vscode = acquireVsCodeApi();

let allLines = [];
let nextOffset = 0;
let hasMore = false;
let currentView = 'pretty';
let currentSearchTerm = '';
let fileInfo = null;
let tokenCounts = new Map();
let currentTokenizer = 'gpt-4';

const MAX_PATHS = 2000;
const MAX_PATH_DEPTH = 8;
const MAX_ARRAY_SCAN = 20;
const AUTO_EXPAND_LIMIT = 50;
let availablePaths = new Set();
let selectedPaths = new Set();
let pathLimitReached = false;
let pathPanelVisible = false;

// Initialize
document.getElementById('pretty-view-btn').addEventListener('click', () => switchView('pretty'));
document.getElementById('render-view-btn').addEventListener('click', () => switchView('render'));
document.getElementById('table-view-btn').addEventListener('click', () => switchView('table'));
document.getElementById('raw-view-btn').addEventListener('click', () => switchView('raw'));
document.getElementById('search-btn').addEventListener('click', performSearch);
document.getElementById('clear-search-btn').addEventListener('click', clearSearch);
document.getElementById('load-more-btn').addEventListener('click', loadMore);
document.getElementById('jump-btn').addEventListener('click', jumpToLine);
document.getElementById('tokenizer-select').addEventListener('change', handleTokenizerChange);
document.getElementById('edit-btn').addEventListener('click', openInTextEditor);
document.getElementById('path-toggle-btn').addEventListener('click', togglePathPanel);
document.getElementById('path-select-all').addEventListener('click', selectAllPaths);
document.getElementById('path-clear').addEventListener('click', clearSelectedPaths);

document.getElementById('search-input').addEventListener('keypress', (e) => {
    if (e.key === 'Enter') performSearch();
});

document.getElementById('jump-line-input').addEventListener('keypress', (e) => {
    if (e.key === 'Enter') jumpToLine();
});

function switchView(view) {
    currentView = view;
    
    // Hide all views
    document.getElementById('pretty-container').style.display = 'none';
    document.getElementById('render-container').style.display = 'none';
    document.getElementById('table-container').style.display = 'none';
    document.getElementById('raw-container').style.display = 'none';
    
    // Remove active from all buttons
    document.getElementById('pretty-view-btn').classList.remove('active');
    document.getElementById('render-view-btn').classList.remove('active');
    document.getElementById('table-view-btn').classList.remove('active');
    document.getElementById('raw-view-btn').classList.remove('active');
    
    // Show selected view
    if (view === 'pretty') {
        document.getElementById('pretty-container').style.display = 'block';
        document.getElementById('pretty-view-btn').classList.add('active');
        renderPretty(allLines, true);
    } else if (view === 'render') {
        document.getElementById('render-container').style.display = 'block';
        document.getElementById('render-view-btn').classList.add('active');
        renderChat(allLines, true);
    } else if (view === 'table') {
        document.getElementById('table-container').style.display = 'block';
        document.getElementById('table-view-btn').classList.add('active');
        renderTable();
    } else if (view === 'raw') {
        document.getElementById('raw-container').style.display = 'block';
        document.getElementById('raw-view-btn').classList.add('active');
        renderRaw();
    }
}

function handleTokenizerChange(e) {
    currentTokenizer = e.target.value;
    // Reload data with new tokenizer
    allLines = [];
    nextOffset = 0;
    resetAvailablePaths();
    clearContainer();
    vscode.postMessage({ type: 'loadLines', offset: 0, limit: 100, searchTerm: currentSearchTerm, tokenizer: currentTokenizer });
    showLoading(true);
}

function openInTextEditor() {
    vscode.postMessage({ type: 'openInTextEditor' });
}

function performSearch() {
    const searchTerm = document.getElementById('search-input').value;
    if (searchTerm.trim()) {
        currentSearchTerm = searchTerm;
        allLines = [];
        nextOffset = 0;
        resetAvailablePaths();
        clearContainer();
        vscode.postMessage({ type: 'loadLines', offset: 0, limit: 100, searchTerm, tokenizer: currentTokenizer });
        showLoading(true);
    }
}

function clearSearch() {
    currentSearchTerm = '';
    document.getElementById('search-input').value = '';
    allLines = [];
    nextOffset = 0;
    resetAvailablePaths();
    clearContainer();
    vscode.postMessage({ type: 'loadLines', offset: 0, limit: 100, tokenizer: currentTokenizer });
    showLoading(true);
}

function loadMore() {
    vscode.postMessage({ type: 'loadLines', offset: nextOffset, limit: 100, searchTerm: currentSearchTerm, tokenizer: currentTokenizer });
    showLoading(true);
}

function jumpToLine() {
    const lineNum = parseInt(document.getElementById('jump-line-input').value);
    if (!isNaN(lineNum) && lineNum >= 0) {
        allLines = [];
        nextOffset = lineNum;
        resetAvailablePaths();
        clearContainer();
        vscode.postMessage({ type: 'jumpToLine', lineNumber: lineNum, tokenizer: currentTokenizer });
        showLoading(true);
    }
}

function clearContainer() {
    document.getElementById('pretty-container').innerHTML = '';
    document.getElementById('render-container').innerHTML = '';
    document.getElementById('table-body').innerHTML = '';
    document.getElementById('table-head').innerHTML = '';
    document.getElementById('raw-container').innerHTML = '';
}

function resetAvailablePaths() {
    availablePaths = new Set();
    pathLimitReached = false;
    if (pathPanelVisible) {
        renderPathList();
    }
}

function showLoading(show) {
    document.getElementById('loading').style.display = show ? 'block' : 'none';
    document.getElementById('load-more-container').style.display = 'none';
}

// Handle messages from extension
window.addEventListener('message', event => {
    const message = event.data;
    
    switch (message.type) {
        case 'fileInfo':
            fileInfo = message;
            document.getElementById('file-name').textContent = message.fileName;
            document.getElementById('file-size').textContent = `(${message.fileSizeMB} MB)`;

            // Show format badge if format is present
            if (message.format) {
                const formatBadge = document.getElementById('format-badge');
                formatBadge.textContent = message.format.toUpperCase();
                formatBadge.style.display = 'inline-block';

                // Disable Edit button for binary formats (Parquet)
                const editBtn = document.getElementById('edit-btn');
                if (message.format === 'parquet') {
                    editBtn.disabled = true;
                    editBtn.title = 'Parquet files are binary and cannot be edited as text';
                    editBtn.style.opacity = '0.5';
                    editBtn.style.cursor = 'not-allowed';
                } else {
                    editBtn.disabled = false;
                    editBtn.title = 'Open in text editor';
                    editBtn.style.opacity = '1';
                    editBtn.style.cursor = 'pointer';
                }
            }
            break;
            
        case 'lines':
            showLoading(false);
            allLines = allLines.concat(message.lines);
            nextOffset = message.nextOffset;
            hasMore = message.hasMore;

            updatePathsFromLines(message.lines);
            
            if (currentView === 'pretty') {
                renderPretty(message.lines);
            } else if (currentView === 'render') {
                renderChat(message.lines);
            } else if (currentView === 'table') {
                renderTable();
            } else if (currentView === 'raw') {
                renderRaw();
            }
            
            updateStats();
            
            if (hasMore) {
                document.getElementById('load-more-container').style.display = 'block';
            }
            break;
            
        case 'tokens':
            // Update token counts asynchronously
            if (message.counts) {
                for (const [lineIndex, count] of Object.entries(message.counts)) {
                    const idx = parseInt(lineIndex);
                    tokenCounts.set(idx, count);
                
                // Update pretty view
                const cardTokenEl = document.getElementById(`tokens-${idx}`);
                if (cardTokenEl) {
                    cardTokenEl.textContent = `${count.toLocaleString()} tokens`;
                }

                // Update table view
                const tableCellEl = document.getElementById(`tokens-cell-${idx}`);
                if (tableCellEl) {
                    tableCellEl.textContent = count.toLocaleString();
                }
                }
            }
            updateStats();
            break;
            
        case 'error':
            showLoading(false);
            alert(message.message);
            break;
    }
});

function togglePathPanel() {
    pathPanelVisible = !pathPanelVisible;
    const panel = document.getElementById('path-panel');
    panel.style.display = pathPanelVisible ? 'block' : 'none';
    if (pathPanelVisible) {
        renderPathList();
    }
}

// Close dropdown when clicking outside
document.addEventListener('click', (e) => {
    const panel = document.getElementById('path-panel');
    const btn = document.getElementById('path-toggle-btn');
    if (pathPanelVisible && !panel.contains(e.target) && e.target !== btn) {
        pathPanelVisible = false;
        panel.style.display = 'none';
    }
});

function selectAllPaths() {
    selectedPaths = new Set(availablePaths);
    renderPathList();
    rerenderPretty();
    rerenderRender();
}

function clearSelectedPaths() {
    selectedPaths.clear();
    renderPathList();
    rerenderPretty();
    rerenderRender();
}

function updatePathCount(total) {
    const countEl = document.getElementById('path-count');
    const suffix = pathLimitReached ? ' (truncated)' : '';
    countEl.textContent = selectedPaths.size + '/' + total + ' selected' + suffix;
}

function buildPathTree(paths) {
    const tree = {};
    paths.forEach(path => {
        // Split by dots, but preserve [] notation
        const parts = path.split('.').map(p => p.trim()).filter(p => p);
        let current = tree;
        let fullPath = '';
        
        parts.forEach((part, index) => {
            if (index > 0) fullPath += '.';
            fullPath += part;
            
            if (!current[part]) {
                current[part] = {
                    fullPath: fullPath,
                    children: {},
                    isArray: part.endsWith('[]')
                };
            }
            current = current[part].children;
        });
    });
    return tree;
}

function getAllDescendantPaths(path) {
    const descendants = [];
    availablePaths.forEach(p => {
        if (p !== path && p.startsWith(path + '.')) {
            descendants.push(p);
        }
    });
    return descendants;
}

function renderPathTree(tree, container, depth = 0) {
    const keys = Object.keys(tree).sort();
    
    keys.forEach(key => {
        const node = tree[key];
        const path = node.fullPath;
        
        const label = document.createElement('label');
        label.className = 'path-item';
        label.style.paddingLeft = (depth * 16) + 'px';

        const checkbox = document.createElement('input');
        checkbox.type = 'checkbox';
        checkbox.checked = selectedPaths.has(path);
        checkbox.addEventListener('change', (e) => {
            e.stopPropagation();
            
            if (checkbox.checked) {
                selectedPaths.add(path);
                // Also select all descendants
                const descendants = getAllDescendantPaths(path);
                descendants.forEach(d => selectedPaths.add(d));
            } else {
                selectedPaths.delete(path);
                // Also deselect all descendants
                const descendants = getAllDescendantPaths(path);
                descendants.forEach(d => selectedPaths.delete(d));
            }
            
            renderPathList();
            rerenderPretty();
            rerenderRender();
        });

        const text = document.createElement('span');
        // Display array fields with (array) notation
        if (key.endsWith('[]')) {
            text.textContent = key.slice(0, -2) + ' (array)';
        } else {
            text.textContent = key;
        }

        label.appendChild(checkbox);
        label.appendChild(text);
        container.appendChild(label);
        
        // Render children
        if (Object.keys(node.children).length > 0) {
            renderPathTree(node.children, container, depth + 1);
        }
    });
}

function renderPathList() {
    const list = document.getElementById('path-list');
    const paths = Array.from(new Set([...availablePaths, ...selectedPaths])).sort();
    updatePathCount(paths.length);

    list.innerHTML = '';
    if (paths.length === 0) {
        const empty = document.createElement('div');
        empty.className = 'path-empty';
        empty.textContent = 'No paths discovered yet.';
        list.appendChild(empty);
        return;
    }

    const tree = buildPathTree(paths);
    renderPathTree(tree, list);
}

function updatePathsFromLines(lines) {
    let added = false;
    lines.forEach(line => {
        if (line.error || line.data === null || line.data === undefined) return;
        if (collectPaths(line.data, '', 0)) {
            added = true;
        }
    });
    if ((added || pathLimitReached) && pathPanelVisible) {
        renderPathList();
    }
}

function addPath(path) {
    if (!path) return false;
    if (availablePaths.has(path)) return false;
    if (availablePaths.size >= MAX_PATHS) {
        pathLimitReached = true;
        return false;
    }
    availablePaths.add(path);
    selectedPaths.add(path); // Auto-select all paths by default
    return true;
}

function collectPaths(value, path, depth) {
    if (pathLimitReached || depth > MAX_PATH_DEPTH) return false;
    let added = false;

    if (value === null || typeof value !== 'object') {
        if (path) {
            added = addPath(path) || added;
        }
        return added;
    }

    if (Array.isArray(value)) {
        // Only use the array notation (path[]) to avoid duplicates
        const arrayPath = path ? path + '[]' : '[]';
        added = addPath(arrayPath) || added;
        const scanLength = Math.min(value.length, MAX_ARRAY_SCAN);
        for (let i = 0; i < scanLength; i++) {
            added = collectPaths(value[i], arrayPath, depth + 1) || added;
            if (pathLimitReached) break;
        }
        return added;
    }

    if (path) {
        added = addPath(path) || added;
    }

    const keys = Object.keys(value);
    for (const key of keys) {
        const childPath = path ? path + '.' + key : key;
        added = collectPaths(value[key], childPath, depth + 1) || added;
        if (pathLimitReached) break;
    }

    return added;
}

function filterValueForPaths(value, path) {
    if (selectedPaths.size === 0) return value;
    if (path && selectedPaths.has(path)) return value;

    if (value === null || typeof value !== 'object') {
        return selectedPaths.has(path) ? value : undefined;
    }

    if (Array.isArray(value)) {
        const arrayPath = path ? path + '[]' : '[]';
        if (selectedPaths.has(arrayPath)) return value;
        const filtered = [];
        for (let i = 0; i < value.length; i++) {
            const item = filterValueForPaths(value[i], arrayPath);
            if (item !== undefined) {
                filtered.push(item);
            }
        }
        return filtered.length ? filtered : undefined;
    }

    const result = {};
    Object.keys(value).forEach(key => {
        const childPath = path ? path + '.' + key : key;
        const childValue = filterValueForPaths(value[key], childPath);
        if (childValue !== undefined) {
            result[key] = childValue;
        }
    });

    return Object.keys(result).length ? result : undefined;
}

function rerenderPretty() {
    if (currentView === 'pretty') {
        renderPretty(allLines, true);
    }
}

function rerenderRender() {
    if (currentView === 'render') {
        renderChat(allLines, true);
    }
}

function renderPretty(lines, reset = false) {
    const container = document.getElementById('pretty-container');
    if (reset) {
        container.innerHTML = '';
    }

    lines.forEach(line => {
        const card = document.createElement('div');
        card.className = line.error ? 'card card-error' : 'card';

        const header = document.createElement('div');
        header.className = 'card-header';

        const title = document.createElement('div');
        title.className = 'card-title';
        title.textContent = 'Line ' + line.index;

        const tokensSpan = document.createElement('span');
        tokensSpan.className = 'card-tokens';
        tokensSpan.id = 'tokens-' + line.index;

        const tokenCount = line.tokens || tokenCounts.get(line.index);
        if (tokenCount !== undefined) {
            tokensSpan.textContent = tokenCount.toLocaleString() + ' tokens';
        } else {
            tokensSpan.textContent = '...';
        }

        header.appendChild(title);
        header.appendChild(tokensSpan);

        const content = document.createElement('div');
        content.className = 'card-content';

        if (line.error) {
            const errorMsg = document.createElement('div');
            errorMsg.className = 'error-message';
            errorMsg.textContent = 'Malformed JSON';
            content.appendChild(errorMsg);
            content.appendChild(document.createTextNode(line.raw));
        } else {
            const filtered = filterValueForPaths(line.data, '');
            if (filtered === undefined) {
                const placeholder = document.createElement('div');
                placeholder.className = 'json-placeholder';
                placeholder.textContent = 'No matching paths for this record.';
                content.appendChild(placeholder);
            } else {
                const tree = renderJsonTree(filtered, 0, null, null);
                if (tree) {
                    tree.classList.add('json-tree');
                    content.appendChild(tree);
                }
            }
        }

        card.appendChild(header);
        card.appendChild(content);
        container.appendChild(card);
    });
}

function renderChat(lines, reset = false) {
    const container = document.getElementById('render-container');
    if (reset) {
        container.innerHTML = '';
    }

    lines.forEach(line => {
        const card = document.createElement('div');
        card.className = line.error ? 'card card-error' : 'card';

        const header = document.createElement('div');
        header.className = 'card-header';

        const title = document.createElement('div');
        title.className = 'card-title';
        title.textContent = 'Line ' + line.index;

        const tokensSpan = document.createElement('span');
        tokensSpan.className = 'card-tokens';
        tokensSpan.id = 'tokens-' + line.index;

        const tokenCount = line.tokens || tokenCounts.get(line.index);
        if (tokenCount !== undefined) {
            tokensSpan.textContent = tokenCount.toLocaleString() + ' tokens';
        } else {
            tokensSpan.textContent = '...';
        }

        header.appendChild(title);
        header.appendChild(tokensSpan);

        const content = document.createElement('div');
        content.className = 'card-content';

        if (line.error) {
            const errorMsg = document.createElement('div');
            errorMsg.className = 'error-message';
            errorMsg.textContent = 'Malformed JSON';
            content.appendChild(errorMsg);
            content.appendChild(document.createTextNode(line.raw));
        } else {
            const filtered = filterValueForPaths(line.data, '');
            
            // Check for Gemini format (text_input/output)
            if (filtered && (filtered.text_input !== undefined || filtered.output !== undefined)) {
                const thread = document.createElement('div');
                thread.className = 'chat-thread';
                const fragment = document.createDocumentFragment();

                // Render text_input as user message
                if (filtered.text_input !== undefined) {
                    const bubble = document.createElement('div');
                    bubble.className = 'chat-bubble user';

                    const roleLabel = document.createElement('div');
                    roleLabel.className = 'chat-role';
                    roleLabel.textContent = 'user';

                    const body = document.createElement('div');
                    body.className = 'chat-content';
                    body.innerHTML = renderMarkdown(String(filtered.text_input || ''));
                    renderLatexInElement(body);

                    bubble.appendChild(roleLabel);
                    bubble.appendChild(body);
                    fragment.appendChild(bubble);
                }

                // Render output as assistant message
                if (filtered.output !== undefined) {
                    const bubble = document.createElement('div');
                    bubble.className = 'chat-bubble assistant';

                    const roleLabel = document.createElement('div');
                    roleLabel.className = 'chat-role';
                    roleLabel.textContent = 'assistant';

                    const body = document.createElement('div');
                    body.className = 'chat-content';
                    body.innerHTML = renderMarkdown(String(filtered.output || ''));
                    renderLatexInElement(body);

                    bubble.appendChild(roleLabel);
                    bubble.appendChild(body);
                    fragment.appendChild(bubble);
                }

                thread.appendChild(fragment);
                content.appendChild(thread);
            } else {
                // Handle standard chat format (messages array)
                const messages = filtered && filtered.messages;
                if (!messages || !Array.isArray(messages)) {
                    // Fallback: Show JSON tree for non-chat data (like Parquet tabular data)
                    if (filtered !== undefined && filtered !== null) {
                        const fallbackLabel = document.createElement('div');
                        fallbackLabel.className = 'json-placeholder';
                        fallbackLabel.style.marginBottom = '8px';
                        fallbackLabel.style.fontStyle = 'italic';
                        fallbackLabel.textContent = 'Data is not in chat format. Showing as JSON:';
                        content.appendChild(fallbackLabel);

                        const tree = renderJsonTree(filtered, 0, null, null);
                        if (tree) {
                            tree.classList.add('json-tree');
                            content.appendChild(tree);
                        }
                    } else {
                        const placeholder = document.createElement('div');
                        placeholder.className = 'json-placeholder';
                        placeholder.textContent = 'No matching data for this record.';
                        content.appendChild(placeholder);
                    }
                } else {
                    const thread = document.createElement('div');
                    thread.className = 'chat-thread';
                    const fragment = document.createDocumentFragment();

                    messages.forEach((message) => {
                        const role = normalizeRole(message && message.role ? message.role : 'unknown');
                        const bubble = document.createElement('div');
                        bubble.className = 'chat-bubble ' + role;

                        const roleLabel = document.createElement('div');
                        roleLabel.className = 'chat-role';
                        roleLabel.textContent = role;

                        const body = document.createElement('div');
                        body.className = 'chat-content';
                        body.innerHTML = renderMarkdown(normalizeMessageContent(message && message.content));
                        renderLatexInElement(body);

                        bubble.appendChild(roleLabel);
                        bubble.appendChild(body);
                        fragment.appendChild(bubble);
                    });

                    thread.appendChild(fragment);
                    content.appendChild(thread);
                }
            }
        }

        card.appendChild(header);
        card.appendChild(content);
        container.appendChild(card);
    });
}

function renderJsonTree(value, depth, label, labelType) {
    if (value === null || typeof value !== 'object') {
        return renderPrimitiveLine(value, depth, label, labelType);
    }
    if (Array.isArray(value)) {
        return renderArrayNode(value, depth, label, labelType);
    }
    return renderObjectNode(value, depth, label, labelType);
}

function getMarkdownRenderer() {
    if (!window.markdownit) {
        return null;
    }
    if (window.__markdownRenderer) {
        return window.__markdownRenderer;
    }
    const renderer = window.markdownit({
        html: false,
        linkify: true,
        breaks: true,
    });
    window.__markdownRenderer = renderer;
    return renderer;
}

function renderMarkdown(text) {
    const renderer = getMarkdownRenderer();
    if (!renderer) {
    return escapeHtml(text).replace(/\\n/g, '<br>');
    }
    return renderer.render(text || '');
}

function renderLatexInElement(element) {
    if (typeof renderMathInElement === 'function') {
        try {
            renderMathInElement(element, {
                delimiters: [
                    {left: '$$', right: '$$', display: true},
                    {left: '$', right: '$', display: false},
                    {left: '\\\\[', right: '\\\\]', display: true},
                    {left: '\\\\(', right: '\\\\)', display: false}
                ],
                throwOnError: false
            });
        } catch (e) {
            console.warn('LaTeX rendering failed:', e);
        }
    }
}

function normalizeRole(role) {
    const normalized = String(role || 'unknown').toLowerCase();
    if (normalized === 'user' || normalized === 'assistant' || normalized === 'system' || normalized === 'tool') {
        return normalized;
    }
    return 'assistant';
}

function normalizeMessageContent(content) {
    if (content === null || content === undefined) {
        return '';
    }
    if (Array.isArray(content)) {
        const parts = [];
        content.forEach(part => {
            if (typeof part === 'string') {
                parts.push(part);
                return;
            }
            if (part && typeof part === 'object') {
                if (part.type === 'text' && typeof part.text === 'string') {
                    parts.push(part.text);
                } else if (part.type === 'input_text' && typeof part.text === 'string') {
                    parts.push(part.text);
                } else if (part.type === 'image_url' && part.image_url && part.image_url.url) {
                    parts.push('[image] ' + part.image_url.url);
                } else {
                    parts.push(JSON.stringify(part));
                }
                return;
            }
            parts.push(String(part));
        });
        return parts.join('\\n');
    }
    if (typeof content === 'string') {
        return content;
    }
    return JSON.stringify(content, null, 2);
}

function escapeHtml(value) {
    return String(value || '')
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;')
        .replace(/"/g, '&quot;')
        .replace(/'/g, '&#39;');
}

function renderPrimitiveLine(value, depth, label, labelType) {
    const line = document.createElement('div');
    line.className = 'json-line';
    line.style.marginLeft = (depth * 16) + 'px';

    if (label !== null && label !== undefined) {
        appendLabel(line, label, labelType);
    }

    const valueSpan = createValueSpan(value);
    line.appendChild(valueSpan);
    return line;
}

function renderObjectNode(obj, depth, label, labelType) {
    const keys = Object.keys(obj);
    if (keys.length === 0) {
        return renderEmptyContainer('{}', depth, label, labelType);
    }

    const details = document.createElement('details');
    details.className = 'json-details';
    details.open = keys.length <= AUTO_EXPAND_LIMIT;
    details.style.marginLeft = (depth * 16) + 'px';

    const summary = document.createElement('summary');
    summary.className = 'json-summary';
    if (label !== null && label !== undefined) {
        appendLabel(summary, label, labelType);
    }
    summary.appendChild(createBraceSpan('{'));
    const meta = document.createElement('span');
    meta.className = 'json-meta';
    meta.textContent = keys.length + ' keys';
    summary.appendChild(meta);
    summary.appendChild(createBraceSpan('}'));
    details.appendChild(summary);

    const renderChildren = () => {
        if (details.dataset.rendered === 'true') return;
        details.dataset.rendered = 'true';
        keys.forEach(key => {
            const child = renderJsonTree(obj[key], depth + 1, key, 'key');
            if (child) {
                details.appendChild(child);
            }
        });
        details.appendChild(renderClosingBrace('}', depth));
    };

    if (details.open) {
        renderChildren();
    }
    details.addEventListener('toggle', () => {
        if (details.open) {
            renderChildren();
        }
    });

    return details;
}

function renderArrayNode(arr, depth, label, labelType) {
    if (arr.length === 0) {
        return renderEmptyContainer('[]', depth, label, labelType);
    }

    const details = document.createElement('details');
    details.className = 'json-details';
    details.open = arr.length <= AUTO_EXPAND_LIMIT;
    details.style.marginLeft = (depth * 16) + 'px';

    const summary = document.createElement('summary');
    summary.className = 'json-summary';
    if (label !== null && label !== undefined) {
        appendLabel(summary, label, labelType);
    }
    summary.appendChild(createBraceSpan('['));
    const meta = document.createElement('span');
    meta.className = 'json-meta';
    meta.textContent = arr.length + ' items';
    summary.appendChild(meta);
    summary.appendChild(createBraceSpan(']'));
    details.appendChild(summary);

    const renderChildren = () => {
        if (details.dataset.rendered === 'true') return;
        details.dataset.rendered = 'true';
        arr.forEach((item, index) => {
            const child = renderJsonTree(item, depth + 1, '[' + index + ']', 'index');
            if (child) {
                details.appendChild(child);
            }
        });
        details.appendChild(renderClosingBrace(']', depth));
    };

    if (details.open) {
        renderChildren();
    }
    details.addEventListener('toggle', () => {
        if (details.open) {
            renderChildren();
        }
    });

    return details;
}

function renderEmptyContainer(braces, depth, label, labelType) {
    const line = document.createElement('div');
    line.className = 'json-line';
    line.style.marginLeft = (depth * 16) + 'px';

    if (label !== null && label !== undefined) {
        appendLabel(line, label, labelType);
    }
    line.appendChild(createBraceSpan(braces));
    return line;
}

function renderClosingBrace(brace, depth) {
    const line = document.createElement('div');
    line.className = 'json-line';
    line.style.marginLeft = (depth * 16) + 'px';
    line.appendChild(createBraceSpan(brace));
    return line;
}

function appendLabel(container, label, labelType) {
    const labelSpan = document.createElement('span');
    if (labelType === 'index') {
        labelSpan.className = 'json-index';
        labelSpan.textContent = label;
    } else {
        labelSpan.className = 'json-key';
        labelSpan.textContent = '\"' + label + '\"';
    }
    container.appendChild(labelSpan);
    container.appendChild(document.createTextNode(': '));
}

function createValueSpan(value) {
    const span = document.createElement('span');
    if (value === null) {
        span.className = 'json-null';
        span.textContent = 'null';
        return span;
    }
    const type = typeof value;
    if (type === 'string') {
        span.className = 'json-string';
        span.textContent = JSON.stringify(value);
    } else if (type === 'number') {
        span.className = 'json-number';
        span.textContent = String(value);
    } else if (type === 'boolean') {
        span.className = 'json-boolean';
        span.textContent = value ? 'true' : 'false';
    } else {
        span.className = 'json-string';
        span.textContent = JSON.stringify(value);
    }
    return span;
}

function createBraceSpan(char) {
    const span = document.createElement('span');
    span.className = 'json-brace';
    span.textContent = char;
    return span;
}

function renderTable() {
    if (allLines.length === 0) return;
    
    const thead = document.getElementById('table-head');
    const tbody = document.getElementById('table-body');
    
    // Extract unique columns from all loaded lines
    const columns = new Set(['_line', '_tokens']);
    allLines.forEach(line => {
        if (line.data && typeof line.data === 'object') {
            Object.keys(line.data).forEach(key => columns.add(key));
        }
    });
    
    const columnArray = Array.from(columns);
    
    // ALWAYS clear and rebuild both header and body for clean render
    thead.innerHTML = '';
    tbody.innerHTML = '';
    
    // Create header with type indicators for schema columns
    const headerRow = document.createElement('tr');
    columnArray.forEach(col => {
        const th = document.createElement('th');
        if (col === '_line') {
            th.textContent = 'Line';
            th.className = 'line-number-col';
        } else if (col === '_tokens') {
            th.textContent = 'Tokens';
            th.className = 'tokens-col';
        } else {
            th.textContent = col;

            // Add type indicator if schema is available
            if (fileInfo && fileInfo.schema && fileInfo.schema.columns) {
                const schemaCol = fileInfo.schema.columns.find(c => c.name === col);
                if (schemaCol) {
                    const typeBadge = document.createElement('span');
                    typeBadge.style.cssText = 'margin-left: 6px; padding: 1px 4px; border-radius: 2px; font-size: 9px; font-weight: normal; background: var(--vscode-badge-background); color: var(--vscode-badge-foreground); opacity: 0.8;';
                    typeBadge.textContent = schemaCol.type;
                    th.appendChild(typeBadge);
                }
            }
        }
        headerRow.appendChild(th);
    });
    thead.appendChild(headerRow);
    
    // Render all rows (always rebuild completely)
    allLines.forEach(line => {
        const tr = document.createElement('tr');
        
        columnArray.forEach(col => {
            const td = document.createElement('td');
            
            if (col === '_line') {
                td.textContent = line.index;
                td.className = 'line-number-col';
            } else if (col === '_tokens') {
                td.className = 'tokens-col';
                td.id = `tokens-cell-${line.index}`;
                const count = line.tokens || tokenCounts.get(line.index);
                if (count !== undefined) {
                    td.textContent = count.toLocaleString();
                } else {
                    td.textContent = '...';
                }
            } else if (line.data && line.data[col] !== undefined) {
                const value = line.data[col];
                if (typeof value === 'object') {
                    td.textContent = JSON.stringify(value);
                    td.title = JSON.stringify(value, null, 2);
                } else {
                    td.textContent = String(value);
                    td.title = String(value);
                }
            } else {
                td.textContent = '';
            }
            
            tr.appendChild(td);
        });
        
        tbody.appendChild(tr);
    });
}

function renderRaw() {
    const container = document.getElementById('raw-container');

    // Show schema for Parquet files (only once at the top)
    if (fileInfo && fileInfo.format === 'parquet' && fileInfo.schema && container.children.length === 0) {
        const schemaDiv = document.createElement('div');
        schemaDiv.style.cssText = 'padding: 16px; margin-bottom: 16px; background: var(--vscode-editor-background); border: 1px solid var(--vscode-widget-border); border-radius: 4px;';

        const schemaHeader = document.createElement('div');
        schemaHeader.style.cssText = 'font-weight: bold; margin-bottom: 12px; color: var(--vscode-foreground);';
        schemaHeader.textContent = '📊 Schema Information';
        schemaDiv.appendChild(schemaHeader);

        if (fileInfo.schema.columns && fileInfo.schema.columns.length > 0) {
            const table = document.createElement('table');
            table.style.cssText = 'width: 100%; border-collapse: collapse; font-family: var(--vscode-editor-font-family); font-size: 12px;';

            // Create table header using DOM methods (no innerHTML for CSP compliance)
            const thead = document.createElement('thead');
            const headerRow = document.createElement('tr');

            const th1 = document.createElement('th');
            th1.style.cssText = 'text-align: left; padding: 8px; border-bottom: 1px solid var(--vscode-widget-border);';
            th1.textContent = 'Column Name';
            headerRow.appendChild(th1);

            const th2 = document.createElement('th');
            th2.style.cssText = 'text-align: left; padding: 8px; border-bottom: 1px solid var(--vscode-widget-border);';
            th2.textContent = 'Type';
            headerRow.appendChild(th2);

            const th3 = document.createElement('th');
            th3.style.cssText = 'text-align: left; padding: 8px; border-bottom: 1px solid var(--vscode-widget-border);';
            th3.textContent = 'Nullable';
            headerRow.appendChild(th3);

            thead.appendChild(headerRow);
            table.appendChild(thead);

            // Create table body using DOM methods (no innerHTML for CSP compliance)
            const tbody = document.createElement('tbody');
            fileInfo.schema.columns.forEach(col => {
                const row = document.createElement('tr');

                const td1 = document.createElement('td');
                td1.style.cssText = 'padding: 8px; border-bottom: 1px solid var(--vscode-widget-border);';
                td1.textContent = col.name;
                row.appendChild(td1);

                const td2 = document.createElement('td');
                td2.style.cssText = 'padding: 8px; border-bottom: 1px solid var(--vscode-widget-border); color: var(--vscode-terminal-ansiBlue);';
                td2.textContent = col.type;
                row.appendChild(td2);

                const td3 = document.createElement('td');
                td3.style.cssText = 'padding: 8px; border-bottom: 1px solid var(--vscode-widget-border);';
                td3.textContent = col.nullable ? 'Yes' : 'No';
                row.appendChild(td3);

                tbody.appendChild(row);
            });
            table.appendChild(tbody);
            schemaDiv.appendChild(table);
        }

        container.appendChild(schemaDiv);
    }

    // Only render new lines (incremental rendering for performance)
    const existingLines = container.children.length;
    allLines.slice(existingLines).forEach(line => {
        const lineDiv = document.createElement('div');
        lineDiv.className = 'raw-line';

        const lineNum = document.createElement('span');
        lineNum.className = 'raw-line-number';
        lineNum.textContent = line.index;

        const content = document.createElement('span');
        content.className = 'raw-line-content';
        // For Parquet, show pretty-printed JSON
        if (fileInfo && fileInfo.format === 'parquet') {
            content.textContent = JSON.stringify(line.data, null, 2);
        } else {
            content.textContent = line.raw;
        }

        lineDiv.appendChild(lineNum);
        lineDiv.appendChild(content);
        container.appendChild(lineDiv);
    });
}

function updateStats() {
    document.getElementById('loaded-count').textContent = allLines.length.toLocaleString();
    
    const counts = Array.from(tokenCounts.values());
    if (counts.length > 0) {
        const avg = Math.round(counts.reduce((a, b) => a + b, 0) / counts.length);
        const max = Math.max(...counts);
        document.getElementById('avg-tokens').textContent = avg.toLocaleString();
        document.getElementById('max-tokens').textContent = max.toLocaleString();
    }
}
