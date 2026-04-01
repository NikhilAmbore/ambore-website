import Link from 'next/link';
import { Zap } from 'lucide-react';

export const metadata = {
  title: 'Terms of Service | Ambore',
};

export default function TermsPage() {
  return (
    <div className="min-h-screen bg-[#09090B] px-4 py-12">
      <div className="max-w-3xl mx-auto">
        <Link href="/" className="flex items-center gap-2 mb-10">
          <div className="w-8 h-8 bg-[#F97316] rounded-lg flex items-center justify-center">
            <Zap className="w-4 h-4 text-white" />
          </div>
          <span className="font-bold text-lg text-[#F8FAFC]">Ambore</span>
        </Link>

        <h1 className="text-3xl font-bold text-[#F8FAFC] mb-2">Terms of Service</h1>
        <p className="text-[#94A3B8] text-sm mb-10">Last updated: March 2026</p>

        <div className="prose prose-invert max-w-none space-y-8 text-[#CBD5E1] text-sm leading-relaxed">
          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">1. Acceptance of Terms</h2>
            <p>By accessing or using Ambore (&quot;the Service&quot;), you agree to be bound by these Terms of Service. If you do not agree, please do not use the Service.</p>
          </section>

          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">2. Description of Service</h2>
            <p>Ambore is an AI-powered career platform that provides resume analysis, ATS scoring, cover letter generation, interview preparation, and job matching services. The Service uses artificial intelligence to provide suggestions and insights about your career documents.</p>
          </section>

          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">3. User Accounts</h2>
            <p>You must create an account to access most features. You are responsible for maintaining the confidentiality of your credentials and for all activities that occur under your account. You must provide accurate and complete information when creating your account.</p>
          </section>

          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">4. Acceptable Use</h2>
            <p>You agree not to:</p>
            <ul className="list-disc pl-6 mt-2 space-y-1">
              <li>Use the Service for any unlawful purpose</li>
              <li>Upload malicious content or attempt to breach our security</li>
              <li>Scrape, crawl, or otherwise harvest data from the Service</li>
              <li>Impersonate any person or entity</li>
              <li>Share your account credentials with others</li>
            </ul>
          </section>

          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">5. AI-Generated Content</h2>
            <p>The Service uses AI to generate content including cover letters, resume suggestions, and interview answers. This content is provided as-is for informational purposes. We do not guarantee the accuracy, completeness, or fitness for any particular purpose of AI-generated content. You are solely responsible for reviewing and editing any AI-generated content before use.</p>
          </section>

          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">6. Data and Privacy</h2>
            <p>Your use of the Service is also governed by our <Link href="/privacy" className="text-[#F97316] hover:text-[#FB923C]">Privacy Policy</Link>, which is incorporated into these Terms by reference.</p>
          </section>

          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">7. Intellectual Property</h2>
            <p>The Service and its original content, features, and functionality are owned by Ambore and are protected by intellectual property laws. You retain ownership of any content you upload to the Service.</p>
          </section>

          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">8. Limitation of Liability</h2>
            <p>Ambore is provided &quot;as is&quot; without warranties of any kind. We are not liable for any indirect, incidental, special, or consequential damages arising from your use of the Service. Our total liability to you for any claim shall not exceed the amount you paid us in the past 12 months.</p>
          </section>

          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">9. Changes to Terms</h2>
            <p>We reserve the right to modify these terms at any time. We will notify users of material changes via email or through the Service. Continued use after changes constitutes acceptance of the new terms.</p>
          </section>

          <section>
            <h2 className="text-lg font-semibold text-[#F8FAFC] mb-3">10. Contact</h2>
            <p>For questions about these Terms, contact us at <span className="text-[#F97316]">support@ambore.io</span>.</p>
          </section>
        </div>

        <div className="mt-12 pt-8 border-t border-white/[0.08]">
          <Link href="/" className="text-sm text-[#94A3B8] hover:text-[#F8FAFC] transition-colors">← Back to Ambore</Link>
        </div>
      </div>
    </div>
  );
}
