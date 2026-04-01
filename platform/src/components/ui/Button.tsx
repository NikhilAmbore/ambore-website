'use client';

import React from 'react';
import { cn } from '@/lib/utils';
import LoadingSpinner from './LoadingSpinner';

export type ButtonVariant = 'primary' | 'secondary' | 'ghost' | 'destructive' | 'outline';
export type ButtonSize = 'sm' | 'md' | 'lg';

interface ButtonProps extends React.ButtonHTMLAttributes<HTMLButtonElement> {
  variant?: ButtonVariant;
  size?: ButtonSize;
  loading?: boolean;
  leftIcon?: React.ReactNode;
  rightIcon?: React.ReactNode;
  fullWidth?: boolean;
}

const variantStyles: Record<ButtonVariant, string> = {
  primary:
    'bg-[#F97316] hover:bg-[#EA6D09] text-white shadow-md hover:shadow-[0_0_20px_rgba(249,115,22,0.4)] active:scale-[0.98]',
  secondary:
    'bg-[#2563EB] hover:bg-[#1D4ED8] text-white shadow-md hover:shadow-[0_0_20px_rgba(37,99,235,0.4)] active:scale-[0.98]',
  ghost:
    'bg-transparent hover:bg-white/5 text-[#94A3B8] hover:text-[#F8FAFC] border border-transparent hover:border-white/10',
  destructive:
    'bg-[#EF4444] hover:bg-[#DC2626] text-white active:scale-[0.98]',
  outline:
    'bg-transparent border border-white/10 hover:border-white/25 text-[#F8FAFC] hover:bg-white/5 active:scale-[0.98]',
};

const sizeStyles: Record<ButtonSize, string> = {
  sm: 'h-8 px-3 text-sm gap-1.5 rounded-[6px]',
  md: 'h-10 px-4 text-sm gap-2 rounded-[6px]',
  lg: 'h-12 px-6 text-base gap-2 rounded-[8px]',
};

const Button = React.forwardRef<HTMLButtonElement, ButtonProps>(
  (
    {
      variant = 'primary',
      size = 'md',
      loading = false,
      leftIcon,
      rightIcon,
      fullWidth = false,
      disabled,
      className,
      children,
      ...props
    },
    ref
  ) => {
    return (
      <button
        ref={ref}
        disabled={disabled || loading}
        className={cn(
          'inline-flex items-center justify-center font-medium transition-all duration-200 select-none whitespace-nowrap',
          variantStyles[variant],
          sizeStyles[size],
          fullWidth && 'w-full',
          (disabled || loading) && 'opacity-50 cursor-not-allowed pointer-events-none',
          className
        )}
        {...props}
      >
        {loading ? (
          <>
            <LoadingSpinner size="sm" />
            <span>{children}</span>
          </>
        ) : (
          <>
            {leftIcon && <span className="shrink-0">{leftIcon}</span>}
            {children}
            {rightIcon && <span className="shrink-0">{rightIcon}</span>}
          </>
        )}
      </button>
    );
  }
);

Button.displayName = 'Button';

export default Button;
