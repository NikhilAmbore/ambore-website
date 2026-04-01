'use client';

import { useState, useEffect, useRef } from 'react';
import Link from 'next/link';
import { usePathname } from 'next/navigation';
import { useSession, signOut } from 'next-auth/react';
import { motion, AnimatePresence } from 'framer-motion';
import {
  Zap, Menu, X, ChevronDown, LayoutDashboard, LogOut,
  FileText, PenLine, MessageSquare, Briefcase, Linkedin, TrendingUp, Target,
} from 'lucide-react';

const TOOLS = [
  { label: 'Resume Analyzer', href: '/resume', icon: FileText, desc: 'ATS score + keyword gaps', color: '#F97316', bg: 'bg-[#F97316]/10' },
  { label: 'Cover Letter', href: '/cover-letter', icon: PenLine, desc: 'AI-tailored in seconds', color: '#F59E0B', bg: 'bg-[#F59E0B]/10' },
  { label: 'Interview Prep', href: '/interview', icon: MessageSquare, desc: 'STAR method answers', color: '#A78BFA', bg: 'bg-[#A78BFA]/10' },
  { label: 'LinkedIn Optimizer', href: '/linkedin', icon: Linkedin, desc: 'Headline & summary rewrite', color: '#60A5FA', bg: 'bg-[#60A5FA]/10' },
  { label: 'Job Board', href: '/jobs', icon: Briefcase, desc: '60K+ US job listings', color: '#34D399', bg: 'bg-[#34D399]/10' },
  { label: 'Career Score', href: '/career-score', icon: TrendingUp, desc: 'Track your job readiness', color: '#FB923C', bg: 'bg-[#FB923C]/10' },
];

export default function Navbar() {
  const { data: session } = useSession();
  const pathname = usePathname();
  const [scrolled, setScrolled] = useState(false);
  const [mobileOpen, setMobileOpen] = useState(false);
  const [toolsOpen, setToolsOpen] = useState(false);
  const [userMenuOpen, setUserMenuOpen] = useState(false);
  const toolsRef = useRef<HTMLDivElement>(null);
  const userRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    const handleScroll = () => setScrolled(window.scrollY > 20);
    window.addEventListener('scroll', handleScroll, { passive: true });
    return () => window.removeEventListener('scroll', handleScroll);
  }, []);

  // Close dropdowns on outside click
  useEffect(() => {
    const handler = (e: MouseEvent) => {
      if (toolsRef.current && !toolsRef.current.contains(e.target as Node)) setToolsOpen(false);
      if (userRef.current && !userRef.current.contains(e.target as Node)) setUserMenuOpen(false);
    };
    document.addEventListener('mousedown', handler);
    return () => document.removeEventListener('mousedown', handler);
  }, []);

  // Close mobile menu on route change
  useEffect(() => { setMobileOpen(false); }, [pathname]);

  const userInitials = session?.user?.name
    ? session.user.name.split(' ').map((n) => n[0]).join('').toUpperCase().slice(0, 2)
    : session?.user?.email?.[0]?.toUpperCase() ?? 'U';

  const isToolActive = TOOLS.some(t => pathname === t.href);

  return (
    <nav className={`fixed top-0 left-0 right-0 z-50 transition-all duration-300 ${
      scrolled ? 'bg-[#09090B]/90 backdrop-blur-xl border-b border-white/[0.08] shadow-lg' : 'bg-transparent'
    }`}>
      <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8">
        <div className="flex items-center justify-between h-16">

          {/* Logo */}
          <Link href="/" className="flex items-center gap-2 group shrink-0">
            <div className="w-8 h-8 bg-[#F97316] rounded-lg flex items-center justify-center shadow-[0_0_15px_rgba(249,115,22,0.4)] group-hover:shadow-[0_0_20px_rgba(249,115,22,0.6)] transition-all">
              <Zap className="w-4 h-4 text-white" />
            </div>
            <span className="font-bold text-lg text-[#F8FAFC]">Ambore</span>
          </Link>

          {/* Desktop Nav */}
          <div className="hidden md:flex items-center gap-1">
            {/* Tools Dropdown */}
            <div ref={toolsRef} className="relative">
              <button
                onClick={() => { setToolsOpen(!toolsOpen); setUserMenuOpen(false); }}
                className={`flex items-center gap-1.5 px-3 py-2 rounded-lg text-sm font-medium transition-all ${
                  isToolActive || toolsOpen
                    ? 'text-[#F97316] bg-[#F97316]/10'
                    : 'text-[#94A3B8] hover:text-[#F8FAFC] hover:bg-white/5'
                }`}
              >
                <Target className="w-3.5 h-3.5" />
                Tools
                <ChevronDown className={`w-3.5 h-3.5 transition-transform duration-200 ${toolsOpen ? 'rotate-180' : ''}`} />
              </button>

              <AnimatePresence>
                {toolsOpen && (
                  <motion.div
                    initial={{ opacity: 0, y: -8, scale: 0.97 }}
                    animate={{ opacity: 1, y: 0, scale: 1 }}
                    exit={{ opacity: 0, y: -8, scale: 0.97 }}
                    transition={{ duration: 0.15 }}
                    className="absolute left-0 top-full mt-2 w-[420px] bg-[#0D0D0F] border border-white/[0.1] rounded-2xl shadow-2xl overflow-hidden"
                  >
                    <div className="p-2">
                      <p className="text-[10px] font-semibold text-[#475569] uppercase tracking-wider px-3 pt-2 pb-1">AI Career Tools</p>
                      <div className="grid grid-cols-2 gap-1">
                        {TOOLS.map(tool => {
                          const Icon = tool.icon;
                          const isActive = pathname === tool.href;
                          return (
                            <Link
                              key={tool.href}
                              href={tool.href}
                              onClick={() => setToolsOpen(false)}
                              className={`flex items-center gap-3 px-3 py-2.5 rounded-xl transition-all group ${
                                isActive ? 'bg-white/[0.06]' : 'hover:bg-white/[0.04]'
                              }`}
                            >
                              <div className={`w-8 h-8 ${tool.bg} rounded-lg flex items-center justify-center shrink-0`}>
                                <Icon className="w-4 h-4" style={{ color: tool.color }} />
                              </div>
                              <div className="min-w-0">
                                <p className={`text-sm font-medium leading-tight ${isActive ? 'text-[#F8FAFC]' : 'text-[#CBD5E1] group-hover:text-[#F8FAFC]'}`}>
                                  {tool.label}
                                </p>
                                <p className="text-xs text-[#64748B] leading-tight mt-0.5">{tool.desc}</p>
                              </div>
                              {isActive && (
                                <div className="ml-auto w-1.5 h-1.5 rounded-full shrink-0" style={{ backgroundColor: tool.color }} />
                              )}
                            </Link>
                          );
                        })}
                      </div>
                    </div>
                    <div className="border-t border-white/[0.06] px-4 py-3 bg-white/[0.02]">
                      <Link
                        href="/dashboard"
                        onClick={() => setToolsOpen(false)}
                        className="flex items-center justify-between text-xs text-[#64748B] hover:text-[#F97316] transition-colors"
                      >
                        <span>View all tools in Dashboard</span>
                        <ChevronDown className="w-3 h-3 -rotate-90" />
                      </Link>
                    </div>
                  </motion.div>
                )}
              </AnimatePresence>
            </div>

            <Link href="/jobs" className={`px-3 py-2 rounded-lg text-sm font-medium transition-all ${
              pathname === '/jobs' ? 'text-[#F97316] bg-[#F97316]/10' : 'text-[#94A3B8] hover:text-[#F8FAFC] hover:bg-white/5'
            }`}>
              Jobs
            </Link>
            <a href="#pricing" className="px-3 py-2 rounded-lg text-sm font-medium text-[#94A3B8] hover:text-[#F8FAFC] hover:bg-white/5 transition-all">
              Pricing
            </a>
          </div>

          {/* Desktop Auth */}
          <div className="hidden md:flex items-center gap-2">
            {session ? (
              <div ref={userRef} className="relative">
                <button
                  onClick={() => { setUserMenuOpen(!userMenuOpen); setToolsOpen(false); }}
                  className="flex items-center gap-2 px-3 py-1.5 rounded-lg hover:bg-white/5 transition-colors"
                >
                  <div className="w-7 h-7 rounded-full bg-[#F97316]/20 border border-[#F97316]/30 flex items-center justify-center text-xs font-semibold text-[#FB923C]">
                    {userInitials}
                  </div>
                  <span className="text-sm text-[#CBD5E1] max-w-[120px] truncate">
                    {session.user?.name?.split(' ')[0] ?? session.user?.email?.split('@')[0]}
                  </span>
                  <ChevronDown className={`w-3.5 h-3.5 text-[#94A3B8] transition-transform ${userMenuOpen ? 'rotate-180' : ''}`} />
                </button>

                <AnimatePresence>
                  {userMenuOpen && (
                    <motion.div
                      initial={{ opacity: 0, y: -8, scale: 0.95 }}
                      animate={{ opacity: 1, y: 0, scale: 1 }}
                      exit={{ opacity: 0, y: -8, scale: 0.95 }}
                      transition={{ duration: 0.15 }}
                      className="absolute right-0 top-full mt-2 w-52 bg-[#0D0D0F] border border-white/10 rounded-xl shadow-2xl overflow-hidden"
                    >
                      <div className="px-4 py-3 border-b border-white/[0.06]">
                        <p className="text-sm font-medium text-[#F8FAFC] truncate">{session.user?.name ?? 'User'}</p>
                        <p className="text-xs text-[#64748B] truncate">{session.user?.email}</p>
                      </div>
                      <div className="py-1">
                        <Link href="/dashboard" onClick={() => setUserMenuOpen(false)}
                          className="flex items-center gap-3 px-4 py-2.5 text-sm text-[#CBD5E1] hover:bg-white/5 hover:text-white transition-colors">
                          <LayoutDashboard className="w-4 h-4 shrink-0" /> Dashboard
                        </Link>
                        <Link href="/resume" onClick={() => setUserMenuOpen(false)}
                          className="flex items-center gap-3 px-4 py-2.5 text-sm text-[#CBD5E1] hover:bg-white/5 hover:text-white transition-colors">
                          <FileText className="w-4 h-4 shrink-0" /> Resume Analyzer
                        </Link>
                        <Link href="/career-score" onClick={() => setUserMenuOpen(false)}
                          className="flex items-center gap-3 px-4 py-2.5 text-sm text-[#CBD5E1] hover:bg-white/5 hover:text-white transition-colors">
                          <TrendingUp className="w-4 h-4 shrink-0" /> Career Score
                        </Link>
                      </div>
                      <div className="border-t border-white/[0.06] py-1">
                        <button
                          onClick={() => { setUserMenuOpen(false); signOut({ callbackUrl: '/' }); }}
                          className="w-full flex items-center gap-3 px-4 py-2.5 text-sm text-[#EF4444] hover:bg-[#EF4444]/10 transition-colors"
                        >
                          <LogOut className="w-4 h-4 shrink-0" /> Sign Out
                        </button>
                      </div>
                    </motion.div>
                  )}
                </AnimatePresence>
              </div>
            ) : (
              <>
                <Link href="/auth/signin"
                  className="px-3 py-2 text-sm text-[#94A3B8] hover:text-[#F8FAFC] transition-colors">
                  Sign In
                </Link>
                <Link href="/auth/signup"
                  className="h-9 px-4 bg-[#F97316] hover:bg-[#EA6D09] text-white text-sm font-semibold rounded-lg flex items-center transition-all shadow-[0_0_15px_rgba(249,115,22,0.3)] hover:shadow-[0_0_20px_rgba(249,115,22,0.5)]">
                  Get Started Free
                </Link>
              </>
            )}
          </div>

          {/* Mobile hamburger */}
          <button
            onClick={() => setMobileOpen(!mobileOpen)}
            className="md:hidden p-2 text-[#94A3B8] hover:text-white transition-colors"
            aria-label="Toggle menu"
          >
            {mobileOpen ? <X className="w-5 h-5" /> : <Menu className="w-5 h-5" />}
          </button>
        </div>
      </div>

      {/* Mobile Menu */}
      <AnimatePresence>
        {mobileOpen && (
          <motion.div
            initial={{ opacity: 0, height: 0 }}
            animate={{ opacity: 1, height: 'auto' }}
            exit={{ opacity: 0, height: 0 }}
            transition={{ duration: 0.2 }}
            className="md:hidden bg-[#09090B]/98 backdrop-blur-xl border-b border-white/[0.08] overflow-hidden"
          >
            <div className="px-4 py-4 max-h-[80vh] overflow-y-auto">
              {/* Tools section */}
              <p className="text-[10px] font-semibold text-[#475569] uppercase tracking-wider mb-2">Tools</p>
              <div className="grid grid-cols-2 gap-1.5 mb-4">
                {TOOLS.map(tool => {
                  const Icon = tool.icon;
                  return (
                    <Link key={tool.href} href={tool.href}
                      className="flex items-center gap-2.5 p-3 rounded-xl bg-white/[0.03] border border-white/[0.06] hover:bg-white/[0.06] transition-all">
                      <div className={`w-7 h-7 ${tool.bg} rounded-lg flex items-center justify-center shrink-0`}>
                        <Icon className="w-3.5 h-3.5" style={{ color: tool.color }} />
                      </div>
                      <span className="text-xs font-medium text-[#CBD5E1]">{tool.label}</span>
                    </Link>
                  );
                })}
              </div>

              {/* Other nav */}
              <div className="space-y-1 border-t border-white/[0.06] pt-3 mb-4">
                <a href="#pricing" className="block py-2 px-2 text-sm text-[#94A3B8] hover:text-white transition-colors rounded-lg hover:bg-white/5">
                  Pricing
                </a>
              </div>

              {/* Auth */}
              {session ? (
                <div className="border-t border-white/[0.06] pt-3 space-y-2">
                  <div className="flex items-center gap-3 px-2 py-2">
                    <div className="w-8 h-8 rounded-full bg-[#F97316]/20 border border-[#F97316]/30 flex items-center justify-center text-xs font-semibold text-[#FB923C]">
                      {userInitials}
                    </div>
                    <div>
                      <p className="text-sm font-medium text-[#F8FAFC]">{session.user?.name ?? 'User'}</p>
                      <p className="text-xs text-[#64748B]">{session.user?.email}</p>
                    </div>
                  </div>
                  <Link href="/dashboard"
                    className="flex items-center gap-3 px-2 py-2.5 text-sm text-[#CBD5E1] hover:text-white rounded-lg hover:bg-white/5 transition-colors">
                    <LayoutDashboard className="w-4 h-4" /> Dashboard
                  </Link>
                  <button
                    onClick={() => signOut({ callbackUrl: '/' })}
                    className="w-full flex items-center gap-3 px-2 py-2.5 text-sm text-[#EF4444] rounded-lg hover:bg-[#EF4444]/10 transition-colors">
                    <LogOut className="w-4 h-4" /> Sign Out
                  </button>
                </div>
              ) : (
                <div className="border-t border-white/[0.06] pt-3 flex flex-col gap-2">
                  <Link href="/auth/signin"
                    className="h-11 flex items-center justify-center text-sm font-medium text-[#CBD5E1] border border-white/10 rounded-xl hover:bg-white/5 transition-all">
                    Sign In
                  </Link>
                  <Link href="/auth/signup"
                    className="h-11 flex items-center justify-center text-sm font-semibold text-white bg-[#F97316] hover:bg-[#EA6D09] rounded-xl transition-all shadow-[0_0_15px_rgba(249,115,22,0.3)]">
                    Get Started Free
                  </Link>
                </div>
              )}
            </div>
          </motion.div>
        )}
      </AnimatePresence>
    </nav>
  );
}
