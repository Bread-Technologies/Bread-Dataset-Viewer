// Disable sharp (image processing) in HuggingFace Transformers - not needed for tokenization
// This prevents native module loading errors on remote machines
process.env.DISABLE_SHARP = '1';

import { AutoTokenizer } from '@huggingface/transformers';
import * as path from 'path';
import { TelemetryService } from '../telemetry/TelemetryService';
import { isTelemetryConfigured } from '../config/telemetry.config';

/**
 * Tokenizer configuration for bundled local tokenizers
 */
interface TokenizerConfig {
    name: string;
    modelId: string;  // HuggingFace model ID (for reference only - we load from disk)
    notes?: string;
}

/**
 * Exhaustive list of supported tokenizers
 * All models are carefully selected to avoid authentication requirements
 * Organized by model family with consistent naming
 */
const TOKENIZER_CONFIGS: { [key: string]: TokenizerConfig } = {
    // ========================================================
    // QWEN FAMILY
    // ========================================================
    
    'qwen-3': {
        name: 'Qwen 3.x',
        modelId: 'Qwen/Qwen3-8B',
        notes: 'Vocab: 36T | Template: Qwen ChatML v3',
    },
    
    'qwen-2.5': {
        name: 'Qwen 2.5',
        modelId: 'Qwen/Qwen2.5-72B-Instruct',
        notes: 'Vocab: Qwen | Template: Qwen ChatML v2',
    },
    
    // ========================================================
    // DEEPSEEK FAMILY
    // ========================================================
    
    'deepseek-v3': {
        name: 'DeepSeek V3 / R1',
        modelId: 'deepseek-ai/DeepSeek-V3',
        notes: 'Vocab: 128k | Template: DeepSeek ChatML',
    },
    
    // ========================================================
    // LLAMA FAMILY
    // ========================================================
    
    'llama-3': {
        name: 'Llama 3.x',
        modelId: 'unsloth/Llama-3.3-70B-Instruct',
        notes: 'Vocab: 128k | Template: Llama 3 | Unsloth version (no auth)',
    },
    
    // ========================================================
    // GEMMA FAMILY
    // ========================================================
    
    'gemma-3': {
        name: 'Gemma 3.x',
        modelId: 'unsloth/gemma-3-12b-it',
        notes: 'Vocab: 262k | Template: Gemma 3 Multimodal | Unsloth version',
    },
    
    'gemma-2': {
        name: 'Gemma 2.x',
        modelId: 'unsloth/gemma-2-9b-it',
        notes: 'Vocab: 256k | Template: Gemma 2 | Unsloth version',
    },
    
    // ========================================================
    // MISTRAL FAMILY
    // ========================================================
    
    'mistral-tekken': {
        name: 'Mistral Tekken',
        modelId: 'mistralai/Mistral-Nemo-Instruct-2407',
        notes: 'Vocab: 131k | For: NeMo 12B, Pixtral 12B, Ministral 8B, Small 3',
    },
    
    'mistral-v3': {
        name: 'Mistral V3',
        modelId: 'unsloth/mistral-7b-instruct-v0.3',
        notes: 'Vocab: 32,768 (SentencePiece) | For: Large 2, Codestral 22B, Mixtral 8x22B, 7B v0.3 | Unsloth version',
    },
    
    'mistral-v1': {
        name: 'Mistral V1',
        modelId: 'mistralai/Mistral-7B-Instruct-v0.1',
        notes: 'Vocab: 32,000 (Llama 2 compatible) | For: 7B v0.1, 7B v0.2, Mixtral 8x7B | Legacy',
    },
    
    // ========================================================
    // PHI FAMILY
    // ========================================================
    
    'phi-4': {
        name: 'Phi 4.x',
        modelId: 'microsoft/Phi-4-mini-instruct',
        notes: 'Vocab: 100k | Template: Phi 4',
    },
    
    // ========================================================
    // COMMAND R FAMILY
    // ========================================================
    
    'command-r': {
        name: 'Command R Family',
        modelId: 'Xenova/c4ai-command-r-v01-tokenizer',
        notes: 'Vocab: 256k (Cohere) | Template: Command R | For: R7B, R, R+ | Xenova version',
    },
    
    // ========================================================
    // GPT FAMILY
    // ========================================================
    
    'gpt-5': {
        name: 'GPT-5.x / gpt-oss',
        modelId: 'openai/gpt-oss-20b',
        notes: 'Vocab: o200k_harmony | Template: Harmony (embedded) | Official repo with Thinking tokens',
    },
    
    'gpt-4o': {
        name: 'GPT-4o Family',
        modelId: 'Xenova/gpt-4o',
        notes: 'Vocab: o200k_base | Template: Basic ChatML | For GPT-4o, o1-preview, o1-mini',
    },
    
    'gpt-4': {
        name: 'GPT-4 Classic',
        modelId: 'Xenova/gpt-4',
        notes: 'Vocab: cl100k_base | Template: ChatML | For GPT-4 Turbo, GPT-3.5 Turbo',
    },
    
    'gpt-2': {
        name: 'GPT-2',
        modelId: 'gpt2',
        notes: 'Vocab: 50k BPE | Template: None | Baseline for modern tokenizers',
    },
    
    // ========================================================
    // CLAUDE FAMILY (PROPRIETARY PROXY)
    // ========================================================
    
    'claude': {
        name: 'Claude 3.x / 4.x',
        modelId: 'Xenova/claude-tokenizer',
        notes: 'Community proxy | Template embedded',
    },
};

// Cache loaded tokenizers
const tokenizers = new Map<string, any>();

/**
 * Get or load a tokenizer for the specified model
 */
async function getTokenizer(tokenizerType: string): Promise<any> {
    if (tokenizers.has(tokenizerType)) {
        return tokenizers.get(tokenizerType);
    }
    
    const config = TOKENIZER_CONFIGS[tokenizerType];
    if (!config) {
        const availableTypes = Object.keys(TOKENIZER_CONFIGS)
            .map(k => `  - ${k}: ${TOKENIZER_CONFIGS[k].name}`)
            .join('\n');
        throw new Error(
            `Unknown tokenizer type: "${tokenizerType}"\n\n` +
            `Available types:\n${availableTypes}`
        );
    }
    
    const loadStart = Date.now();

    try {
        // Construct path to bundled tokenizer directory
        // __dirname points to out/utils/, so we go up to extension root, then into tokenizers/
        const localPath = path.join(__dirname, '..', '..', 'tokenizers', tokenizerType);

        // Load from bundled local files only - no network access
        const tokenizer = await AutoTokenizer.from_pretrained(localPath, {
            local_files_only: true,  // Force offline loading from bundled files
        });

        tokenizers.set(tokenizerType, tokenizer);

        // Track successful tokenizer loading
        if (isTelemetryConfigured()) {
            TelemetryService.getInstance().sendEvent('tokenizer.loaded', {
                tokenizerType,
                tokenizerName: config.name,
            }, {
                loadTimeMs: Date.now() - loadStart,
            });
        }

        return tokenizer;
    } catch (error) {
        // Create detailed error message for local loading failures
        const errorMsg = String(error);
        let helpText = '\n\nThe bundled tokenizer files may be missing or corrupted. Try reinstalling the extension.';
        let errorCategory = 'load_failure';

        if (errorMsg.includes('ENOENT') || errorMsg.includes('not found')) {
            helpText = `\n\nTokenizer directory not found: tokenizers/${tokenizerType}/\nThe extension installation may be incomplete.`;
            errorCategory = 'not_found';
        }

        // Track tokenizer loading failure
        if (isTelemetryConfigured()) {
            TelemetryService.getInstance().sendError('error.tokenization', error as Error, {
                errorType: errorCategory,
                tokenizerType,
                tokenizerName: config.name,
                context: 'loading',
            });
        }

        throw new Error(
            `Failed to load bundled tokenizer: ${config.name}\n` +
            `Local key: ${tokenizerType}\n` +
            `Error: ${errorMsg}${helpText}`
        );
    }
}

/**
 * Apply chat template to messages if the data is in chat format
 */
async function applyChatTemplate(data: any, tokenizerType: string): Promise<string> {
    // Check if data has messages array (chat completions format)
    if (data && Array.isArray(data.messages)) {
        const tokenizer = await getTokenizer(tokenizerType);
        const startTime = Date.now();

        try {
            // Use the tokenizer's built-in chat template
            const formatted = await tokenizer.apply_chat_template(data.messages, {
                tokenize: false,
                add_generation_prompt: false,
            });

            // Track successful template application
            if (isTelemetryConfigured()) {
                TelemetryService.getInstance().sendEvent('tokenizer.template.applied', {
                    tokenizerType,
                    tokenizerName: TOKENIZER_CONFIGS[tokenizerType].name,
                }, {
                    messageCount: data.messages.length,
                    durationMs: Date.now() - startTime,
                });
            }

            return formatted;
        } catch (error) {
            const errorStr = String(error);

            // Categorize error type for telemetry
            let errorCategory = 'unknown';
            let guidance = '';

            if (errorStr.includes('chat_template is not set') || errorStr.includes('no template argument')) {
                errorCategory = 'missing_template';
                guidance = '\n\n💡 This tokenizer does not have a chat template configured.\n' +
                          'Solutions:\n' +
                          '  • Switch to "Full JSON" mode to count the raw JSON tokens\n' +
                          '  • Switch to "Key" mode to count a specific field\n' +
                          '  • Use a different model tokenizer';
            } else if (errorStr.includes('System role not supported')) {
                errorCategory = 'system_role_unsupported';
                guidance = '\n\n💡 This model does not support system messages.\n' +
                          'Solutions:\n' +
                          '  • Remove system role messages from your data\n' +
                          '  • Switch to "Full JSON" or "Raw Text" mode\n' +
                          '  • Use a different tokenizer';
            } else if (errorStr.includes('Tool call IDs')) {
                errorCategory = 'tool_call_validation';
                guidance = '\n\n💡 This model has strict tool call validation.\n' +
                          'Solutions:\n' +
                          '  • Fix tool call format in your data\n' +
                          '  • Switch to "Full JSON" or "Raw Text" mode\n' +
                          '  • Use a different tokenizer';
            }

            // Track chat template error
            if (isTelemetryConfigured()) {
                TelemetryService.getInstance().sendError('error.tokenization', error as Error, {
                    errorType: errorCategory,
                    tokenizerType,
                    tokenizerName: TOKENIZER_CONFIGS[tokenizerType].name,
                    context: 'chat_template',
                });
            }

            throw new Error(
                `Chat template error (${TOKENIZER_CONFIGS[tokenizerType].name}):\n${errorStr}${guidance}`
            );
        }
    }
    
    // If not chat format, return original JSON string
    return JSON.stringify(data);
}

export interface TokenCountResult {
    count: number;
    mode: 'chat' | 'full-json' | 'key' | 'raw-text';
    key?: string;  // For mode='key', which key was used
    preview: string;  // First 100 chars of what was tokenized
}

/**
 * Count tokens in text using the specified tokenizer
 * 
 * @param text - Raw text or JSON string
 * @param tokenizerType - Model tokenizer key (e.g., 'qwen-3', 'llama-3', 'gpt-4o')
 * @param mode - Tokenization mode: 'auto', 'chat', 'full-json', 'key:<keyname>', 'raw-text'
 * @returns Token count and metadata about what was tokenized
 * @throws Error if tokenizer fails to load or tokenization fails
 */
export async function countTokens(
    text: string, 
    tokenizerType: string = 'qwen-3',
    mode: string = 'auto'
): Promise<TokenCountResult> {
    const tokenizer = await getTokenizer(tokenizerType);
    
    try {
        let textToTokenize = text;
        let actualMode: TokenCountResult['mode'] = 'raw-text';
        let usedKey: string | undefined;
        
        // Parse JSON if possible
        let parsed: any = null;
        try {
            parsed = JSON.parse(text);
        } catch {
            // Not JSON, use raw text
        }
        
        // Determine what to tokenize based on mode
        if (mode === 'auto') {
            // Auto-detect: prefer messages array with chat template, fallback to full JSON
            if (parsed && Array.isArray(parsed.messages)) {
                try {
                    textToTokenize = await applyChatTemplate(parsed, tokenizerType);
                    actualMode = 'chat';
                } catch (chatError) {
                    // Chat template not available for this tokenizer, fall back to full-json
                    textToTokenize = JSON.stringify(parsed);
                    actualMode = 'full-json';

                    // Track fallback from chat to full-json
                    if (isTelemetryConfigured()) {
                        TelemetryService.getInstance().sendEvent('tokenizer.mode.fallback', {
                            tokenizerType,
                            fromMode: 'chat',
                            toMode: 'full-json',
                            reason: 'template_unavailable',
                        });
                    }
                }
            } else if (parsed) {
                textToTokenize = JSON.stringify(parsed);
                actualMode = 'full-json';
            } else {
                // Keep original text
                actualMode = 'raw-text';
            }
        } else if (mode === 'chat') {
            // Force chat mode
            if (parsed && Array.isArray(parsed.messages)) {
                textToTokenize = await applyChatTemplate(parsed, tokenizerType);
                actualMode = 'chat';
            } else {
                throw new Error('No messages array found for chat mode');
            }
        } else if (mode === 'full-json') {
            // Force full JSON
            if (parsed) {
                textToTokenize = JSON.stringify(parsed);
                actualMode = 'full-json';
            } else {
                throw new Error('Not valid JSON for full-json mode');
            }
        } else if (mode.startsWith('key:')) {
            // Extract specific key
            const keyName = mode.substring(4);
            if (parsed && keyName in parsed) {
                const value = parsed[keyName];
                textToTokenize = typeof value === 'string' ? value : JSON.stringify(value);
                actualMode = 'key';
                usedKey = keyName;
            } else {
                throw new Error(`Key "${keyName}" not found in JSON`);
            }
        } else if (mode === 'raw-text') {
            // Use raw text as-is
            textToTokenize = text;
            actualMode = 'raw-text';
        }
        
        // Tokenize using the actual model tokenizer
        const tokens = await tokenizer.encode(textToTokenize);
        
        return {
            count: tokens.length,
            mode: actualMode,
            key: usedKey,
            preview: textToTokenize.substring(0, 100),
        };
    } catch (error) {
        const errorMsg = String(error);

        // Categorize error for telemetry
        let errorCategory = 'unknown';
        if (errorMsg.includes('chat_template') || errorMsg.includes('template')) {
            errorCategory = 'missing_template';
        } else if (errorMsg.includes('System role')) {
            errorCategory = 'system_role_unsupported';
        } else if (errorMsg.includes('Tool call')) {
            errorCategory = 'tool_call_validation';
        } else if (errorMsg.includes('Key') && errorMsg.includes('not found')) {
            errorCategory = 'key_not_found';
        } else if (errorMsg.includes('Failed to load')) {
            errorCategory = 'load_failure';
        } else if (errorMsg.includes('No messages array')) {
            errorCategory = 'invalid_format';
        } else if (errorMsg.includes('Not valid JSON')) {
            errorCategory = 'invalid_json';
        }

        // Track token counting error
        if (isTelemetryConfigured()) {
            TelemetryService.getInstance().sendError('error.tokenization', error as Error, {
                errorType: errorCategory,
                tokenizerType,
                tokenizerName: TOKENIZER_CONFIGS[tokenizerType].name,
                context: 'counting',
                mode,
            });
        }

        throw new Error(
            `Token counting failed for ${TOKENIZER_CONFIGS[tokenizerType].name}:\n${error}`
        );
    }
}

/**
 * Get tokenizer options for dropdown/quick-pick (id + display name).
 */
export function getTokenizerOptions(): { id: string; label: string }[] {
    return Object.entries(TOKENIZER_CONFIGS).map(([id, config]) => ({
        id,
        label: config.name,
    }));
}

/**
 * Get display name for a tokenizer id, or undefined if unknown.
 */
export function getTokenizerName(id: string): string | undefined {
    return TOKENIZER_CONFIGS[id]?.name;
}

/**
 * Cleanup loaded tokenizers
 */
export function cleanup(): void {
    tokenizers.clear();
}
