// Mock VS Code API
const vscode = {
  Uri: {
    file: (path: string) => ({ fsPath: path, toString: () => path }),
  },
  window: {
    showTextDocument: jest.fn(),
  },
  workspace: {
    openTextDocument: jest.fn(),
  },
  CancellationTokenSource: jest.fn(),
  // Add other mocks as needed
};

// Make vscode available globally
(global as any).vscode = vscode;

// Mock the vscode module for imports
jest.mock('vscode', () => vscode, { virtual: true });
