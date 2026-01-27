import * as vscode from 'vscode';
import * as cp from 'child_process';
import { promisify } from 'util';
import { Backend } from './index';

const exec = promisify(cp.exec);

export class OllamaBackend implements Backend {
    name = 'Ollama';
    private serverProcess: cp.ChildProcess | null = null;

    async isInstalled(): Promise<boolean> {
        try {
            await exec('ollama --version');
            return true;
        } catch {
            return false;
        }
    }

    async isRunning(): Promise<boolean> {
        try {
            const response = await fetch('http://localhost:11434/api/tags', {
                method: 'GET',
            });
            return response.ok;
        } catch {
            return false;
        }
    }

    async install(): Promise<boolean> {
        const platform = process.platform;

        if (platform === 'win32') {
            // Windows: Open browser to download page
            vscode.window.showInformationMessage(
                'Opening Ollama download page. Please install and restart VS Code.',
                'OK'
            );
            vscode.env.openExternal(vscode.Uri.parse('https://ollama.com/download/windows'));
            return false;
        } else {
            // macOS/Linux: Use install script
            const choice = await vscode.window.showInformationMessage(
                'Install Ollama? This will run: curl -fsSL https://ollama.com/install.sh | sh',
                'Install',
                'Cancel'
            );

            if (choice !== 'Install') {
                return false;
            }

            return await vscode.window.withProgress(
                {
                    location: vscode.ProgressLocation.Notification,
                    title: 'Installing Ollama...',
                    cancellable: false,
                },
                async (progress) => {
                    try {
                        progress.report({ message: 'Downloading and installing...' });
                        await exec('curl -fsSL https://ollama.com/install.sh | sh');
                        
                        progress.report({ message: 'Verifying installation...' });
                        const installed = await this.isInstalled();
                        
                        if (installed) {
                            vscode.window.showInformationMessage('Ollama installed successfully!');
                            return true;
                        } else {
                            vscode.window.showErrorMessage('Ollama installation failed. Please install manually from ollama.com');
                            return false;
                        }
                    } catch (error) {
                        vscode.window.showErrorMessage(`Installation failed: ${error}`);
                        return false;
                    }
                }
            );
        }
    }

    async start(): Promise<boolean> {
        if (await this.isRunning()) {
            return true;
        }

        return await vscode.window.withProgress(
            {
                location: vscode.ProgressLocation.Notification,
                title: 'Starting Ollama...',
                cancellable: false,
            },
            async (progress) => {
                try {
                    // Start Ollama serve in background
                    this.serverProcess = cp.spawn('ollama', ['serve'], {
                        detached: true,
                        stdio: 'ignore',
                    });
                    this.serverProcess.unref();

                    // Poll for server to be ready (timeout 30s)
                    const maxAttempts = 30;
                    for (let i = 0; i < maxAttempts; i++) {
                        progress.report({ message: `Waiting for server... (${i + 1}/${maxAttempts})` });
                        await new Promise((resolve) => setTimeout(resolve, 1000));
                        
                        if (await this.isRunning()) {
                            vscode.window.showInformationMessage('Ollama started successfully!');
                            return true;
                        }
                    }

                    vscode.window.showErrorMessage('Ollama failed to start within 30 seconds');
                    return false;
                } catch (error) {
                    vscode.window.showErrorMessage(`Failed to start Ollama: ${error}`);
                    return false;
                }
            }
        );
    }

    async createModel(modelPath: string, modelName: string): Promise<boolean> {
        try {
            const modelfile = `FROM ${modelPath}`;
            
            // Use ollama create command
            const { stdout, stderr } = await exec(
                `echo "${modelfile}" | ollama create ${modelName} -f -`
            );
            
            console.log('Model created:', stdout);
            if (stderr) {
                console.error('Model creation stderr:', stderr);
            }
            
            return true;
        } catch (error) {
            vscode.window.showErrorMessage(`Failed to create model: ${error}`);
            return false;
        }
    }

    async deleteModel(modelName: string): Promise<boolean> {
        try {
            await exec(`ollama rm ${modelName}`);
            return true;
        } catch (error) {
            console.error(`Failed to delete model ${modelName}:`, error);
            return false;
        }
    }

    async chat(modelName: string, messages: any[]): Promise<ReadableStream<Uint8Array>> {
        const response = await fetch('http://localhost:11434/api/chat', {
            method: 'POST',
            headers: {
                'Content-Type': 'application/json',
            },
            body: JSON.stringify({
                model: modelName,
                messages: messages,
                stream: true,
            }),
        });

        if (!response.ok) {
            throw new Error(`Chat request failed: ${response.statusText}`);
        }

        return response.body!;
    }
}
