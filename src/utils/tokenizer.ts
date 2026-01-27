import { get_encoding, encoding_for_model } from 'tiktoken';

const encoders = new Map<string, any>();
let defaultEncoder: any = null;

// Chat template definitions for different models
const chatTemplates: { [key: string]: (messages: any[]) => string } = {
    'llama-3': (messages) => {
        // Llama 3 format: <|begin_of_text|><|start_header_id|>role<|end_header_id|>content<|eot_id|>
        let formatted = '<|begin_of_text|>';
        for (const msg of messages) {
            formatted += `<|start_header_id|>${msg.role}<|end_header_id|>\n\n${msg.content}<|eot_id|>`;
        }
        return formatted;
    },
    'llama-2': (messages) => {
        // Llama 2 format: [INST] <<SYS>>system<</SYS>>user [/INST] assistant
        let formatted = '';
        let systemMsg = '';
        for (let i = 0; i < messages.length; i++) {
            const msg = messages[i];
            if (msg.role === 'system') {
                systemMsg = `<<SYS>>\n${msg.content}\n<</SYS>>\n\n`;
            } else if (msg.role === 'user') {
                formatted += `[INST] ${systemMsg}${msg.content} [/INST] `;
                systemMsg = '';
            } else if (msg.role === 'assistant') {
                formatted += `${msg.content} `;
            }
        }
        return formatted;
    },
    'mistral': (messages) => {
        // Mistral format: <s>[INST] user [/INST] assistant</s>
        let formatted = '<s>';
        for (const msg of messages) {
            if (msg.role === 'user') {
                formatted += `[INST] ${msg.content} [/INST]`;
            } else if (msg.role === 'assistant') {
                formatted += ` ${msg.content}</s>`;
            }
        }
        return formatted;
    },
    'qwen': (messages) => {
        // Qwen format: <|im_start|>role\ncontent<|im_end|>
        let formatted = '';
        for (const msg of messages) {
            formatted += `<|im_start|>${msg.role}\n${msg.content}<|im_end|>\n`;
        }
        return formatted;
    },
    'glm': (messages) => {
        // ChatGLM format: [Round 0]\n问：user\n答：assistant
        let formatted = '';
        let roundNum = 0;
        for (let i = 0; i < messages.length; i += 2) {
            if (i + 1 < messages.length) {
                formatted += `[Round ${roundNum}]\n问：${messages[i].content}\n答：${messages[i + 1].content}\n`;
                roundNum++;
            }
        }
        return formatted;
    },
};

export async function initTokenizer(): Promise<void> {
    // Don't initialize eagerly - let it be lazy loaded on first use
    // This saves 300-500ms on extension activation
}

function getEncoder(tokenizerType: string = 'gpt-4'): any {
    // Return cached encoder if available
    if (encoders.has(tokenizerType)) {
        return encoders.get(tokenizerType);
    }
    
    // Initialize default encoder lazily on first use
    if (!defaultEncoder) {
        try {
            defaultEncoder = encoding_for_model('gpt-4');
        } catch (error) {
            console.error('Failed to initialize default encoder:', error);
        }
    }
    
    try {
        let encoder;
        
        switch (tokenizerType) {
            case 'gpt-4':
            case 'claude':
            case 'llama-3':
            case 'qwen2.5':
                // Use cl100k_base (GPT-4 encoding)
                encoder = get_encoding('cl100k_base');
                break;
            case 'gpt-3':
                // GPT-3 uses p50k_base
                encoder = get_encoding('p50k_base');
                break;
            case 'gpt-2':
            case 'llama-2':
            case 'mistral':
            case 'phi':
                // Use r50k_base (GPT-2 encoding) as approximation
                encoder = get_encoding('r50k_base');
                break;
            case 'qwen':
            case 'glm':
            case 'baichuan':
            case 'yi':
            case 'gemma':
            case 'deepseek':
            case 'internlm':
                // Use cl100k_base as reasonable approximation for Chinese models
                encoder = get_encoding('cl100k_base');
                break;
            default:
                encoder = defaultEncoder;
        }
        
        if (encoder) {
            encoders.set(tokenizerType, encoder);
        }
        return encoder;
    } catch (error) {
        console.error(`Failed to get encoder for ${tokenizerType}:`, error);
        return defaultEncoder;
    }
}

function applyChatTemplate(data: any, tokenizerType: string): string {
    // Check if data has messages array (chat completions format)
    if (data && Array.isArray(data.messages)) {
        const template = chatTemplates[tokenizerType];
        if (template) {
            return template(data.messages);
        }
        // Default: just concatenate messages
        return data.messages.map((m: any) => `${m.role}: ${m.content}`).join('\n');
    }
    // If not chat format, return original JSON string
    return JSON.stringify(data);
}

export function countTokens(text: string, tokenizerType: string = 'gpt-4'): number {
    const encoder = getEncoder(tokenizerType);
    
    if (!encoder) {
        // Fallback to approximation if encoder not ready
        return Math.ceil(text.length / 4);
    }
    
    try {
        // Try to parse as JSON to check for chat completions format
        let textToTokenize = text;
        try {
            const parsed = JSON.parse(text);
            if (parsed && Array.isArray(parsed.messages)) {
                // Apply chat template for accurate token counting
                textToTokenize = applyChatTemplate(parsed, tokenizerType);
            }
        } catch {
            // Not JSON or not chat format, use original text
        }
        
        const tokens = encoder.encode(textToTokenize);
        return tokens.length;
    } catch (error) {
        console.error('Token counting error:', error);
        return Math.ceil(text.length / 4);
    }
}

export function cleanup(): void {
    // Free all encoders
    for (const encoder of encoders.values()) {
        try {
            encoder.free();
        } catch (e) {
            // Ignore errors during cleanup
        }
    }
    encoders.clear();
    
    if (defaultEncoder) {
        try {
            defaultEncoder.free();
        } catch (e) {
            // Ignore
        }
        defaultEncoder = null;
    }
}
