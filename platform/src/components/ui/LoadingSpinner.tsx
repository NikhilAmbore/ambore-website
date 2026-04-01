import React from 'react';
import { cn } from '@/lib/utils';

interface LoadingSpinnerProps {
  size?: 'xs' | 'sm' | 'md' | 'lg' | 'xl';
  color?: string;
  className?: string;
}

const sizeStyles = {
  xs: 'w-3 h-3 border',
  sm: 'w-4 h-4 border-2',
  md: 'w-6 h-6 border-2',
  lg: 'w-8 h-8 border-[3px]',
  xl: 'w-12 h-12 border-4',
};

const LoadingSpinner: React.FC<LoadingSpinnerProps> = ({
  size = 'md',
  color,
  className,
}) => {
  return (
    <div
      className={cn('rounded-full animate-spin', sizeStyles[size], !color && 'border-white/30 border-t-white', className)}
      style={color ? { borderColor: `${color}30`, borderTopColor: color } : undefined}
    />
  );
};

export function FullPageLoader({ message }: { message?: string }) {
  return (
    <div className="fixed inset-0 bg-[#09090B]/80 backdrop-blur-sm flex flex-col items-center justify-center z-50 gap-4">
      <LoadingSpinner size="xl" color="#F97316" />
      {message && <p className="text-[#94A3B8] text-sm">{message}</p>}
    </div>
  );
}

export default LoadingSpinner;
