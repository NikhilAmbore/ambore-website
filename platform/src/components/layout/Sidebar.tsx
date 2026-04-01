'use client';

import { useState } from 'react';
import Link from 'next/link';
import { usePathname } from 'next/navigation';
import { useSession, signOut } from 'next-auth/react';
import {
  Zap,
  LayoutDashboard,
  FileText,
  Briefcase,
  MessageSquare,
  TrendingUp,
  LogOut,
  ChevronLeft,
  ChevronRight,
  Menu,
  PenLine,
  Linkedin,
} from 'lucide-react';
import { cn } from '@/lib/utils';

const navItems = [
  { label: 'Dashboard', href: '/dashboard', icon: LayoutDashboard },
  { label: 'Resume Analyzer', href: '/resume', icon: FileText },
  { label: 'Cover Letter', href: '/cover-letter', icon: PenLine },
  { label: 'Interview Practice', href: '/interview', icon: MessageSquare },
  { label: 'Jobs', href: '/jobs', icon: Briefcase },
  { label: 'LinkedIn Optimizer', href: '/linkedin', icon: Linkedin },
  { label: 'Career Score', href: '/career-score', icon: TrendingUp },
];

export default function Sidebar() {
  const pathname = usePathname();
  const { data: session } = useSession();
  const [collapsed, setCollapsed] = useState(false);
  const [mobileOpen, setMobileOpen] = useState(false);

  const userInitials = session?.user?.name
    ? session.user.name.split(' ').map((n) => n[0]).join('').toUpperCase().slice(0, 2)
    : session?.user?.email?.[0]?.toUpperCase() ?? 'U';

  const SidebarContent = () => (
    <div className="flex flex-col h-full">
      {/* Logo */}
      <div className={cn('flex items-center h-16 px-4 border-b border-white/[0.06]', collapsed ? 'justify-center' : 'gap-2')}>
        <div className="w-8 h-8 bg-[#F97316] rounded-lg flex items-center justify-center shadow-[0_0_15px_rgba(249,115,22,0.4)] shrink-0">
          <Zap className="w-4 h-4 text-white" />
        </div>
        {!collapsed && (
          <span className="font-bold text-lg text-[#F8FAFC]">Ambore</span>
        )}
      </div>

      {/* Nav Items */}
      <nav className="flex-1 py-4 px-3 space-y-1">
        {navItems.map((item) => {
          const Icon = item.icon;
          const isActive = pathname === item.href;

          return (
            <Link
              key={item.href}
              href={item.href}
              onClick={() => setMobileOpen(false)}
              title={collapsed ? item.label : undefined}
              className={cn(
                'flex items-center gap-3 px-3 py-2.5 rounded-lg text-sm font-medium transition-all duration-150',
                isActive
                  ? 'bg-[#F97316]/15 text-[#FB923C] border border-[#F97316]/20'
                  : 'text-[#94A3B8] hover:bg-white/5 hover:text-[#F8FAFC]',
                collapsed && 'justify-center px-2'
              )}
            >
              <Icon className={cn('w-4.5 h-4.5 shrink-0', isActive ? 'text-[#F97316]' : '')} style={{ width: '18px', height: '18px' }} />
              {!collapsed && <span>{item.label}</span>}
            </Link>
          );
        })}
      </nav>

      {/* Collapse toggle (desktop) */}
      <button
        onClick={() => setCollapsed(!collapsed)}
        className="hidden lg:flex items-center justify-center h-8 w-8 mx-auto mb-2 rounded-lg text-[#94A3B8] hover:text-white hover:bg-white/5 transition-colors"
      >
        {collapsed ? <ChevronRight className="w-4 h-4" /> : <ChevronLeft className="w-4 h-4" />}
      </button>

      {/* User info */}
      <div className={cn('border-t border-white/[0.06] p-4', collapsed && 'px-2')}>
        <div className={cn('flex items-center gap-3', collapsed && 'justify-center')}>
          <div className="w-8 h-8 rounded-full bg-[#F97316]/20 border border-[#F97316]/30 flex items-center justify-center text-xs font-semibold text-[#FB923C] shrink-0">
            {userInitials}
          </div>
          {!collapsed && (
            <div className="flex-1 min-w-0">
              <p className="text-sm font-medium text-[#F8FAFC] truncate">
                {session?.user?.name ?? 'User'}
              </p>
              <p className="text-xs text-[#94A3B8] truncate">
                {session?.user?.email}
              </p>
            </div>
          )}
          {!collapsed && (
            <button
              onClick={() => signOut({ callbackUrl: '/' })}
              className="p-1.5 text-[#94A3B8] hover:text-[#EF4444] hover:bg-[#EF4444]/10 rounded-lg transition-colors"
              title="Sign out"
            >
              <LogOut className="w-4 h-4" />
            </button>
          )}
        </div>
        {collapsed && (
          <button
            onClick={() => signOut({ callbackUrl: '/' })}
            className="mt-2 w-full p-1.5 flex justify-center text-[#94A3B8] hover:text-[#EF4444] hover:bg-[#EF4444]/10 rounded-lg transition-colors"
            title="Sign out"
          >
            <LogOut className="w-4 h-4" />
          </button>
        )}
      </div>
    </div>
  );

  return (
    <>
      {/* Mobile toggle button */}
      <button
        onClick={() => setMobileOpen(!mobileOpen)}
        className="lg:hidden fixed top-4 left-4 z-50 p-2 bg-[#131316] border border-white/10 rounded-lg text-[#94A3B8] hover:text-white transition-colors"
      >
        <Menu className="w-5 h-5" />
      </button>

      {/* Mobile overlay */}
      {mobileOpen && (
        <div
          className="lg:hidden fixed inset-0 bg-black/60 backdrop-blur-sm z-40"
          onClick={() => setMobileOpen(false)}
        />
      )}

      {/* Mobile sidebar */}
      <aside
        className={cn(
          'lg:hidden fixed top-0 left-0 h-full z-50 bg-[#0D0D0F] border-r border-white/[0.06] w-64 transition-transform duration-300',
          mobileOpen ? 'translate-x-0' : '-translate-x-full'
        )}
      >
        <SidebarContent />
      </aside>

      {/* Desktop sidebar */}
      <aside
        className={cn(
          'hidden lg:flex flex-col h-screen sticky top-0 bg-[#0D0D0F] border-r border-white/[0.06] transition-all duration-300 shrink-0',
          collapsed ? 'w-[60px]' : 'w-[220px]'
        )}
      >
        <SidebarContent />
      </aside>
    </>
  );
}
