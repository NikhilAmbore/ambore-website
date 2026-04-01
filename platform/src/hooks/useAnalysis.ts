'use client';

import { useState, useCallback } from 'react';
import type { AnalysisResult } from '@/types';
import toast from 'react-hot-toast';

export type AnalysisStepId = 'idle' | 'parsing' | 'matching' | 'optimizing' | 'complete' | 'error';

export interface AnalysisState {
  step: AnalysisStepId;
  result: AnalysisResult | null;
  error: string | null;
  isLoading: boolean;
}

export interface UseAnalysisReturn extends AnalysisState {
  analyze: (resumeText: string, jobDescription: string) => Promise<void>;
  reset: () => void;
  setResult: (result: AnalysisResult) => void;
}

const initialState: AnalysisState = {
  step: 'idle',
  result: null,
  error: null,
  isLoading: false,
};

export function useAnalysis(): UseAnalysisReturn {
  const [state, setState] = useState<AnalysisState>(initialState);

  const analyze = useCallback(async (resumeText: string, jobDescription: string) => {
    if (!resumeText.trim()) {
      toast.error('Please provide resume text');
      return;
    }
    if (!jobDescription.trim() || jobDescription.length < 50) {
      toast.error('Please provide a job description (min 50 characters)');
      return;
    }

    setState({ step: 'parsing', result: null, error: null, isLoading: true });

    try {
      setState((s) => ({ ...s, step: 'matching' }));

      const response = await fetch('/api/resume/analyze', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ resumeText, jobDescription }),
      });

      setState((s) => ({ ...s, step: 'optimizing' }));

      if (!response.ok) {
        const errorData = await response.json();
        throw new Error(errorData.error ?? 'Analysis failed');
      }

      const data = await response.json();

      setState({
        step: 'complete',
        result: data.data,
        error: null,
        isLoading: false,
      });

      toast.success('Analysis complete!');
    } catch (error) {
      const message = error instanceof Error ? error.message : 'Analysis failed';
      setState({
        step: 'error',
        result: null,
        error: message,
        isLoading: false,
      });
      toast.error(message);
    }
  }, []);

  const reset = useCallback(() => {
    setState(initialState);
  }, []);

  const setResult = useCallback((result: AnalysisResult) => {
    setState({ step: 'complete', result, error: null, isLoading: false });
  }, []);

  return {
    ...state,
    analyze,
    reset,
    setResult,
  };
}

export default useAnalysis;
