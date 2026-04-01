import React from 'react';
import { cn } from '@/lib/utils';

export type BadgeVariant = 'default' | 'success' | 'warning' | 'danger' | 'info' | 'orange';

interface BadgeProps extends React.HTMLAttributes<HTMLSpanElement> {
  variant?: BadgeVariant;
  size?: 'sm' | 'md';
}

const variantStyles: Record<BadgeVariant, string> = {
  default: 'bg-white/10 text-[#CBD5E1] border border-white/10',
  success: 'bg-[#22C55E]/15 text-[#4ADE80] border border-[#22C55E]/20',
  warning: 'bg-[#F59E0B]/15 text-[#FCD34D] border border-[#F59E0B]/20',
  danger: 'bg-[#EF4444]/15 text-[#F87171] border border-[#EF4444]/20',
  info: 'bg-[#3B82F6]/15 text-[#60A5FA] border border-[#3B82F6]/20',
  orange: 'bg-[#F97316]/15 text-[#FB923C] border border-[#F97316]/20',
};

const sizeStyles = {
  sm: 'text-xs px-2 py-0.5',
  md: 'text-xs px-2.5 py-1',
};

const Badge = React.forwardRef<HTMLSpanElement, BadgeProps>(
  ({ variant = 'default', size = 'md', className, children, ...props }, ref) => {
    return (
      <span
        ref={ref}
        className={cn(
          'inline-flex items-center font-medium rounded-full',
          variantStyles[variant],
          sizeStyles[size],
          className
        )}
        {...props}
      >
        {children}
      </span>
    );
  }
);

Badge.displayName = 'Badge';

export default Badge;
