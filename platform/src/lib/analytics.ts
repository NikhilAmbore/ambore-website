import { PostHog } from 'posthog-node';

let serverPostHog: PostHog | null = null;

function getServerPostHog(): PostHog | null {
  if (typeof window !== 'undefined') return null;

  if (!process.env.NEXT_PUBLIC_POSTHOG_KEY) return null;

  if (!serverPostHog) {
    serverPostHog = new PostHog(process.env.NEXT_PUBLIC_POSTHOG_KEY, {
      host: process.env.NEXT_PUBLIC_POSTHOG_HOST ?? 'https://app.posthog.com',
      flushAt: 1,
      flushInterval: 0,
    });
  }

  return serverPostHog;
}

export async function trackEvent(
  userId: string,
  event: string,
  properties?: Record<string, unknown>
): Promise<void> {
  const ph = getServerPostHog();
  if (!ph) return;

  ph.capture({
    distinctId: userId,
    event,
    properties: {
      ...properties,
      timestamp: new Date().toISOString(),
    },
  });

  await ph.flush();
}

export async function identifyUser(
  userId: string,
  properties: Record<string, unknown>
): Promise<void> {
  const ph = getServerPostHog();
  if (!ph) return;

  ph.identify({
    distinctId: userId,
    properties,
  });

  await ph.flush();
}
