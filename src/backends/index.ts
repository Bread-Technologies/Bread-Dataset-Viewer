import * as vscode from 'vscode';
import { OllamaBackend } from './ollama';

export interface Backend {
    name: string;
    isInstalled(): Promise<boolean>;
    isRunning(): Promise<boolean>;
    install(): Promise<boolean>;
    start(): Promise<boolean>;
    createModel(modelPath: string, modelName: string): Promise<boolean>;
    deleteModel(modelName: string): Promise<boolean>;
    chat(modelName: string, messages: any[]): Promise<ReadableStream<Uint8Array>>;
}

let currentBackend: Backend | null = null;
let statusBarItem: vscode.StatusBarItem;

export async function initializeBackends(context: vscode.ExtensionContext): Promise<void> {
    // Create status bar item
    statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100);
    statusBarItem.command = 'mlWorkbench.manageBackend';
    context.subscriptions.push(statusBarItem);
    
    // Register command
    context.subscriptions.push(
        vscode.commands.registerCommand('mlWorkbench.manageBackend', handleBackendManagement)
    );
    
    // Try to initialize Ollama
    const ollama = new OllamaBackend();
    if (await ollama.isInstalled()) {
        currentBackend = ollama;
        await updateStatusBar();
    } else {
        updateStatusBarNoBackend();
    }
}

export async function getBackend(): Promise<Backend | null> {
    if (!currentBackend) {
        // Try to initialize
        const ollama = new OllamaBackend();
        if (await ollama.isInstalled()) {
            currentBackend = ollama;
            await updateStatusBar();
        }
    }
    return currentBackend;
}

export async function ensureBackendReady(): Promise<Backend | null> {
    const backend = await getBackend();
    
    if (!backend) {
        // Prompt to install
        const choice = await vscode.window.showInformationMessage(
            'No model runtime found. Install Ollama to chat with local models.',
            'Install Ollama',
            'Cancel'
        );
        
        if (choice === 'Install Ollama') {
            const ollama = new OllamaBackend();
            const success = await ollama.install();
            if (success) {
                currentBackend = ollama;
                await updateStatusBar();
                return currentBackend;
            }
        }
        return null;
    }
    
    // Check if running
    if (!(await backend.isRunning())) {
        const choice = await vscode.window.showInformationMessage(
            'Ollama is not running. Start it?',
            'Start Ollama',
            'Cancel'
        );
        
        if (choice === 'Start Ollama') {
            const success = await backend.start();
            if (success) {
                await updateStatusBar();
                return backend;
            }
        }
        return null;
    }
    
    return backend;
}

async function updateStatusBar(): Promise<void> {
    if (!currentBackend || !statusBarItem) return;
    
    const isRunning = await currentBackend.isRunning();
    
    if (isRunning) {
        statusBarItem.text = `$(vm-running) ${currentBackend.name}`;
        statusBarItem.backgroundColor = undefined;
        statusBarItem.tooltip = `${currentBackend.name} is running and ready`;
    } else {
        statusBarItem.text = `$(vm-outline) ${currentBackend.name}`;
        statusBarItem.backgroundColor = undefined;
        statusBarItem.tooltip = `${currentBackend.name} is installed but not running. Click to manage.`;
    }
    
    statusBarItem.show();
}

function updateStatusBarNoBackend(): void {
    if (!statusBarItem) return;
    
    statusBarItem.text = '$(warning) No runtime';
    statusBarItem.backgroundColor = new vscode.ThemeColor('statusBarItem.warningBackground');
    statusBarItem.tooltip = 'No model runtime installed. Click to install.';
    statusBarItem.show();
}

async function handleBackendManagement(): Promise<void> {
    if (!currentBackend) {
        const choice = await vscode.window.showQuickPick(
            ['Install Ollama'],
            { placeHolder: 'No model runtime found' }
        );
        
        if (choice === 'Install Ollama') {
            const ollama = new OllamaBackend();
            await ollama.install();
            currentBackend = ollama;
            await updateStatusBar();
        }
        return;
    }
    
    const isRunning = await currentBackend.isRunning();
    
    const items = [];
    if (isRunning) {
        items.push({ label: 'Stop', description: `Stop ${currentBackend.name}` });
        items.push({ label: 'Restart', description: `Restart ${currentBackend.name}` });
    } else {
        items.push({ label: 'Start', description: `Start ${currentBackend.name}` });
    }
    items.push({ label: 'Reinstall', description: `Reinstall ${currentBackend.name}` });
    
    const choice = await vscode.window.showQuickPick(items, {
        placeHolder: `Manage ${currentBackend.name}`,
    });
    
    if (choice) {
        switch (choice.label) {
            case 'Start':
                await currentBackend.start();
                await updateStatusBar();
                break;
            case 'Reinstall':
                await currentBackend.install();
                await updateStatusBar();
                break;
        }
    }
}

export function updateBackendStatus(): void {
    if (currentBackend) {
        updateStatusBar();
    } else {
        updateStatusBarNoBackend();
    }
}
