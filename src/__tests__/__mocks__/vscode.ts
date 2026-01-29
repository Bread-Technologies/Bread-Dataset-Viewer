// Mock VS Code API for testing

export const Uri = {
  file: (path: string) => ({
    fsPath: path,
    toString: () => path,
    with: jest.fn(),
  }),
  parse: (path: string) => ({
    fsPath: path,
    toString: () => path,
  }),
};

export const window = {
  showTextDocument: jest.fn(),
  createWebviewPanel: jest.fn(),
  showInformationMessage: jest.fn(),
  showErrorMessage: jest.fn(),
};

export const workspace = {
  openTextDocument: jest.fn(),
  fs: {
    readFile: jest.fn(),
    writeFile: jest.fn(),
  },
};

export const CancellationTokenSource = jest.fn(() => ({
  token: {
    isCancellationRequested: false,
    onCancellationRequested: jest.fn(),
  },
  cancel: jest.fn(),
  dispose: jest.fn(),
}));

export const commands = {
  registerCommand: jest.fn(),
  executeCommand: jest.fn(),
};

export const ViewColumn = {
  One: 1,
  Two: 2,
  Three: 3,
};

export const Webview = jest.fn();
export const WebviewPanel = jest.fn();

// Mock the entire module
export default {
  Uri,
  window,
  workspace,
  CancellationTokenSource,
  commands,
  ViewColumn,
  Webview,
  WebviewPanel,
};
