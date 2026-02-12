/**
 * Telemetry configuration for ML Workbench extension
 *
 * Application Insights keys are designed for client-side use and safe to include
 * in published extensions. Rate limiting and security are handled server-side by Azure.
 *
 * Environment variable (APP_INSIGHTS_KEY) can override for development/testing.
 */

export const TELEMETRY_CONFIG = {
    /**
     * Application Insights connection string
     * Safe to include in source - designed for client-side use
     */
    appInsightsKey: process.env.APP_INSIGHTS_KEY || 'InstrumentationKey=57b31524-522d-4291-aab6-ff38f89ddbdb;IngestionEndpoint=https://westus2-2.in.applicationinsights.azure.com/;LiveEndpoint=https://westus2.livediagnostics.monitor.azure.com/;ApplicationId=bd35885e-0019-417f-96c7-8abe4d62a95e',

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
