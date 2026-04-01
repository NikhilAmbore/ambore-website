import Link from 'next/link';
import { Zap, Linkedin } from 'lucide-react';

const XIcon = () => (
  <svg viewBox="0 0 24 24" className="w-4 h-4" fill="currentColor">
    <path d="M18.244 2.25h3.308l-7.227 8.26 8.502 11.24H16.17l-4.714-6.231-5.401 6.231H2.748l7.73-8.835L1.254 2.25H8.08l4.259 5.631 5.905-5.631zm-1.161 17.52h1.833L7.084 4.126H5.117z" />
  </svg>
);

const GithubIcon = () => (
  <svg viewBox="0 0 24 24" className="w-4 h-4" fill="currentColor">
    <path d="M12 2C6.477 2 2 6.484 2 12.017c0 4.425 2.865 8.18 6.839 9.504.5.092.682-.217.682-.483 0-.237-.008-.868-.013-1.703-2.782.605-3.369-1.343-3.369-1.343-.454-1.158-1.11-1.466-1.11-1.466-.908-.62.069-.608.069-.608 1.003.07 1.531 1.032 1.531 1.032.892 1.53 2.341 1.088 2.91.832.092-.647.35-1.088.636-1.338-2.22-.253-4.555-1.113-4.555-4.951 0-1.093.39-1.988 1.029-2.688-.103-.253-.446-1.272.098-2.65 0 0 .84-.27 2.75 1.026A9.564 9.564 0 0112 6.844c.85.004 1.705.115 2.504.337 1.909-1.296 2.747-1.027 2.747-1.027.546 1.379.202 2.398.1 2.651.64.7 1.028 1.595 1.028 2.688 0 3.848-2.339 4.695-4.566 4.943.359.309.678.92.678 1.855 0 1.338-.012 2.419-.012 2.747 0 .268.18.58.688.482A10.019 10.019 0 0022 12.017C22 6.484 17.522 2 12 2z" />
  </svg>
);

const footerLinks = {
  Tools: [
    { label: 'Resume Analyzer', href: '/resume' },
    { label: 'Cover Letter', href: '/cover-letter' },
    { label: 'Interview Prep', href: '/interview' },
    { label: 'LinkedIn Optimizer', href: '/linkedin' },
    { label: 'Job Board', href: '/jobs' },
    { label: 'Career Score', href: '/career-score' },
  ],
  Company: [
    { label: 'Dashboard', href: '/dashboard' },
    { label: 'Sign Up Free', href: '/auth/signup' },
    { label: 'Sign In', href: '/auth/signin' },
    { label: 'Contact', href: 'mailto:hello@ambore.io' },
  ],
  Legal: [
    { label: 'Privacy Policy', href: '/privacy' },
    { label: 'Terms of Service', href: '/terms' },
  ],
};

const socialLinks = [
  { icon: XIcon, href: 'https://twitter.com/ambore_io', label: 'X (Twitter)' },
  { icon: Linkedin, href: 'https://linkedin.com/company/ambore', label: 'LinkedIn' },
  { icon: GithubIcon, href: 'https://github.com/ambore', label: 'GitHub' },
];

export default function Footer() {
  return (
    <footer className="border-t border-white/[0.06] bg-[#09090B]">
      <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 py-16">
        <div className="grid grid-cols-2 md:grid-cols-5 gap-8 mb-12">
          {/* Brand */}
          <div className="col-span-2">
            <Link href="/" className="flex items-center gap-2 mb-4 w-fit">
              <div className="w-8 h-8 bg-[#F97316] rounded-lg flex items-center justify-center shadow-[0_0_15px_rgba(249,115,22,0.4)]">
                <Zap className="w-4 h-4 text-white" />
              </div>
              <span className="font-bold text-lg text-[#F8FAFC]">Ambore</span>
            </Link>
            <p className="text-sm text-[#94A3B8] leading-relaxed max-w-xs mb-6">
              AI-powered career platform. Analyze resumes, match jobs, generate cover letters, and practice interviews — all in one place.
            </p>
            <div className="flex items-center gap-3">
              {socialLinks.map((social) => {
                const Icon = social.icon;
                return (
                  <a key={social.label} href={social.href} target="_blank" rel="noopener noreferrer"
                    aria-label={social.label}
                    className="w-9 h-9 bg-white/[0.05] border border-white/[0.08] rounded-lg flex items-center justify-center text-[#94A3B8] hover:text-white hover:bg-white/[0.1] hover:border-white/[0.15] transition-all">
                    <Icon className="w-4 h-4" />
                  </a>
                );
              })}
            </div>
          </div>

          {/* Link columns */}
          {Object.entries(footerLinks).map(([category, links]) => (
            <div key={category}>
              <h4 className="text-sm font-semibold text-[#F8FAFC] mb-4">{category}</h4>
              <ul className="space-y-3">
                {links.map((link) => (
                  <li key={link.label}>
                    <Link href={link.href}
                      className="text-sm text-[#94A3B8] hover:text-[#F8FAFC] transition-colors">
                      {link.label}
                    </Link>
                  </li>
                ))}
              </ul>
            </div>
          ))}
        </div>

        {/* Bottom */}
        <div className="pt-8 border-t border-white/[0.06] flex flex-col sm:flex-row items-center justify-between gap-4">
          <p className="text-sm text-[#94A3B8]">
            &copy; {new Date().getFullYear()} Ambore, Inc. All rights reserved.
          </p>
          <p className="text-sm text-[#94A3B8]">
            Built for job seekers everywhere
          </p>
        </div>
      </div>
    </footer>
  );
}
