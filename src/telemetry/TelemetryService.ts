import * as vscode from 'vscode';
import { TelemetryReporter } from '@vscode/extension-telemetry';

/**
 * Singleton telemetry service for tracking user behavior, performance, and errors
 * across the ML Workbench extension.
 *
 * Features:
 * - Session tracking with unique IDs
 * - Performance timing utilities
 * - Error deduplication and throttling
 * - Automatic PII sanitization
 * - Respects user's VS Code telemetry preferences
 */
export class TelemetryService {
    private static instance: TelemetryService | null = null;
    private reporter: TelemetryReporter | null = null;
    private readonly extensionId = 'ml-workbench';
    private readonly extensionVersion: string;

    // Session tracking
    private sessionId: string;
    private sessionStartTime: number;

    // Performance tracking
    private performanceTimers = new Map<string, number>();

    // Error deduplication
    private recentErrors = new Map<string, number>();
    private readonly ERROR_THROTTLE_MS = 60000; // 1 minute

    private constructor(context: vscode.ExtensionContext, appInsightsKey: string) {
        this.extensionVersion = context.extension.packageJSON.version;
        this.reporter = new TelemetryReporter(appInsightsKey);
        this.sessionId = this.generateSessionId();
        this.sessionStartTime = Date.now();

        // Register for disposal
        context.subscriptions.push(this.reporter);

        // Track session start
        this.sendEvent('session.started', {
            sessionId: this.sessionId,
            vscodeVersion: vscode.version,
            platform: process.platform,
            arch: process.arch,
        });
    }

    /**
     * Initialize the telemetry service
     * @param context VS Code extension context
     * @param appInsightsKey Application Insights instrumentation key
     */
    public static initialize(context: vscode.ExtensionContext, appInsightsKey: string): void {
        if (!TelemetryService.instance) {
            TelemetryService.instance = new TelemetryService(context, appInsightsKey);
        }
    }

    /**
     * Get the singleton instance
     */
    public static getInstance(): TelemetryService {
        if (!TelemetryService.instance) {
            throw new Error('TelemetryService not initialized. Call initialize() first.');
        }
        return TelemetryService.instance;
    }

    /**
     * Check if user has telemetry enabled in VS Code settings
     */
    private isTelemetryEnabled(): boolean {
        const config = vscode.workspace.getConfiguration('telemetry');
        const level = config.get<string>('telemetryLevel', 'all');
        return level !== 'off';
    }

    /**
     * Send a telemetry event
     * @param eventName Event name (e.g., 'file.opened', 'tokenizer.selected')
     * @param properties Event properties (strings only)
     * @param measurements Event measurements (numbers only)
     */
    public sendEvent(
        eventName: string,
        properties?: Record<string, string>,
        measurements?: Record<string, number>
    ): void {
        if (!this.reporter || !this.isTelemetryEnabled()) {
            return;
        }

        // Add session context to all events
        const enrichedProperties = {
            ...properties,
            sessionId: this.sessionId,
            extensionVersion: this.extensionVersion,
        };

        this.reporter.sendTelemetryEvent(eventName, enrichedProperties, measurements);
    }

    /**
     * Send an error event with deduplication
     * @param errorName Error event name
     * @param error Error object or message
     * @param properties Additional properties
     */
    public sendError(
        errorName: string,
        error: Error | string,
        properties?: Record<string, string>
    ): void {
        if (!this.reporter || !this.isTelemetryEnabled()) {
            return;
        }

        const errorMessage = error instanceof Error ? error.message : String(error);
        const errorKey = `${errorName}:${errorMessage}`;
        const now = Date.now();
        const lastSent = this.recentErrors.get(errorKey);

        // Throttle duplicate errors
        if (lastSent && (now - lastSent) < this.ERROR_THROTTLE_MS) {
            return;
        }

        this.recentErrors.set(errorKey, now);

        // Sanitize error message (remove file paths, user data)
        const sanitizedMessage = this.sanitizeErrorMessage(errorMessage);

        const enrichedProperties = {
            ...properties,
            errorName,
            errorMessage: sanitizedMessage,
            sessionId: this.sessionId,
            platform: process.platform,
        };

        const measurements: Record<string, number> = {};

        if (error instanceof Error && error.stack) {
            measurements.stackLength = error.stack.split('\n').length;
        }

        this.reporter.sendTelemetryErrorEvent(errorName, enrichedProperties, measurements);
    }

    /**
     * Start a performance timer
     * @param operationId Unique identifier for this operation
     */
    public startTimer(operationId: string): void {
        this.performanceTimers.set(operationId, Date.now());
    }

    /**
     * End a performance timer and send timing event
     * @param operationId Operation identifier (must match startTimer call)
     * @param eventName Event name to send
     * @param properties Additional properties
     */
    public endTimer(
        operationId: string,
        eventName: string,
        properties?: Record<string, string>
    ): void {
        const startTime = this.performanceTimers.get(operationId);
        if (!startTime) {
            return;
        }

        const duration = Date.now() - startTime;
        this.performanceTimers.delete(operationId);

        this.sendEvent(eventName, properties, {
            durationMs: duration,
        });
    }

    /**
     * Sanitize error messages to remove PII (GDPR compliance)
     * @param message Original error message
     * @returns Sanitized message
     */
    private sanitizeErrorMessage(message: string): string {
        if (!message) {
            return '';
        }

        let sanitized = message;

        // Remove Windows file paths (C:\Users\...)
        sanitized = sanitized.replace(/[A-Za-z]:\\[\w\\\s\-\.]+/g, '<PATH>');

        // Remove Unix file paths (/home/user/..., /Users/...)
        sanitized = sanitized.replace(/\/(?:home|Users|root)\/[\w\/\s\-\.]+/g, '<PATH>');

        // Remove other absolute paths
        sanitized = sanitized.replace(/\/[\w\/\-\.]{20,}/g, '<PATH>');

        // Remove email addresses
        sanitized = sanitized.replace(/\b[\w\.-]+@[\w\.-]+\.\w+\b/g, '<EMAIL>');

        // Remove potential API keys or tokens (long alphanumeric strings)
        sanitized = sanitized.replace(/\b[a-zA-Z0-9]{32,}\b/g, '<TOKEN>');

        // Remove UUIDs
        sanitized = sanitized.replace(/\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b/gi, '<UUID>');

        // Truncate to reasonable length
        return sanitized.substring(0, 500);
    }

    /**
     * Generate a unique session ID
     */
    private generateSessionId(): string {
        return `${Date.now()}-${Math.random().toString(36).substring(2, 15)}`;
    }

    /**
     * Dispose of the telemetry service and send session end event
     */
    public dispose(): void {
        if (this.reporter) {
            // Send session end event
            const sessionDuration = Date.now() - this.sessionStartTime;
            this.sendEvent('session.ended', {
                sessionId: this.sessionId,
            }, {
                sessionDurationMs: sessionDuration,
            });

            this.reporter.dispose();
            this.reporter = null;
        }
        TelemetryService.instance = null;
    }
}
