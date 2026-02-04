/**
 * Telemetry configuration for ML Workbench extension
 *
 * IMPORTANT: Replace with your actual Application Insights instrumentation key
 * or use environment variable for production deployments.
 *
 * To create an Application Insights resource:
 * 1. Go to Azure Portal (portal.azure.com)
 * 2. Create new Application Insights resource
 * 3. Copy the Instrumentation Key
 * 4. Set APP_INSIGHTS_KEY environment variable or replace below
 */

export const TELEMETRY_CONFIG = {
    /**
     * Application Insights connection string
     * Must be set via APP_INSIGHTS_KEY environment variable
     */
    appInsightsKey: process.env.APP_INSIGHTS_KEY || '',

    /**
     * Enable/disable telemetry globally (still respects VS Code user setting)
     */
    enableTelemetry: true,

    /**
     * Enable performance tracking (timers, durations)
     */
    enablePerformanceTracking: true,

    /**
     * Enable error tracking
     */
    enableErrorTracking: true,

    /**
     * Event sampling rate (0.0 to 1.0)
     * 1.0 = 100% of events sent
     * 0.5 = 50% of events sent (random sampling)
     */
    eventSamplingRate: 1.0,

    /**
     * Error sampling rate (0.0 to 1.0)
     */
    errorSamplingRate: 1.0,
};

/**
 * Check if telemetry is configured
 */
export function isTelemetryConfigured(): boolean {
    return TELEMETRY_CONFIG.appInsightsKey.length > 0 && TELEMETRY_CONFIG.enableTelemetry;
}
