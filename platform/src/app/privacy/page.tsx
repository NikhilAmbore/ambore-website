import Link from 'next/link';
import { Zap } from 'lucide-react';

export const metadata = {
  title: 'Privacy Policy | Ambore',
};

export default function PrivacyPage() {
  return (
    <div className="min-h-screen bg-[#09090B] px-4 py-12">
      <div className="max-w-3xl mx-auto">
        <Link href="/" className="flex items-center gap-2 mb-10">
          <div className="w-8 h-8 bg-[#F97316] rounded-lg flex items-center justify-center">
            <Zap className="w-4 h-4 text-white" />
          </div>
          <span className="font-bold text-lg text-[#F8FAFC]">Ambore</span>
        </Link>

        <h1 className="text-3xl font-bold text-[#F8FAFC] mb-2">Privacy Policy</h1>
        <p className="text-[#94A3B8] text-sm mb-10">Last updated: March 2026</p>

        <div className="prose prose-invert max-w-none space-y-8 text-[#CBD5E1] text-sm leading-relaxed">
          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">1. Information We Collect</h2>
            <p>We collect information you provide directly:</p>
            <ul className="list-disc pl-6 mt-2 space-y-1">
              <li><strong>Account information:</strong> name, email address, and password (stored as a secure hash)</li>
              <li><strong>Resume content:</strong> text you paste or upload for analysis</li>
              <li><strong>Job descriptions:</strong> content you provide for matching</li>
              <li><strong>Usage data:</strong> features used, analyses performed, scores achieved</li>
            </ul>
            <p className="mt-3">We also collect limited technical data: IP addresses, browser type, and device information for security and debugging purposes.</p>
          </section>

          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">2. How We Use Your Information</h2>
            <ul className="list-disc pl-6 space-y-1">
              <li>Provide and improve the Service</li>
              <li>Generate AI-powered resume analysis, cover letters, and interview prep</li>
              <li>Track your career progress and scores</li>
              <li>Send important account and security notifications</li>
              <li>Prevent fraud and ensure platform security</li>
            </ul>
          </section>

          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">3. Data Sharing</h2>
            <p>We do not sell your personal data. We share data only with:</p>
            <ul className="list-disc pl-6 mt-2 space-y-1">
              <li><strong>OpenAI:</strong> Resume text and job descriptions are sent to OpenAI's API for analysis. OpenAI's data handling is governed by their privacy policy.</li>
              <li><strong>Infrastructure providers:</strong> Database and hosting providers under data processing agreements.</li>
              <li><strong>Legal requirements:</strong> When required by law or to protect our rights.</li>
            </ul>
          </section>

          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">4. Data Retention</h2>
            <p>We retain your account data for as long as your account is active. Resume analyses and activity logs are retained for 12 months. You may delete your account and all associated data at any time by contacting us.</p>
          </section>

          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">5. Security</h2>
            <p>We use industry-standard security measures including encrypted connections (HTTPS), hashed passwords, and access controls. However, no method of transmission over the internet is 100% secure.</p>
          </section>

          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">6. Your Rights</h2>
            <p>You have the right to:</p>
            <ul className="list-disc pl-6 mt-2 space-y-1">
              <li>Access the personal data we hold about you</li>
              <li>Request correction of inaccurate data</li>
              <li>Request deletion of your data</li>
              <li>Export your data in a machine-readable format</li>
              <li>Opt out of non-essential communications</li>
            </ul>
          </section>

          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">7. Cookies</h2>
            <p>We use session cookies for authentication and optional analytics cookies (PostHog). You can disable cookies in your browser settings, though this may affect Service functionality.</p>
          </section>

          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">8. Contact Us</h2>
            <p>For privacy concerns or data requests, contact us at <span className="text-[#F97316]">privacy@ambore.io</span>.</p>
          </section>
        </div>

        <div className="mt-12 pt-8 border-t border-white/[0.08]">
          <Link href="/" className="text-sm text-[#94A3B8] hover:text-[#F8FAFC] transition-colors">← Back to Ambore</Link>
        </div>
      </div>
    </div>
  );
}
