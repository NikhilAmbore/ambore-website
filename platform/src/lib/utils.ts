import { clsx, type ClassValue } from 'clsx';
import { twMerge } from 'tailwind-merge';

export function cn(...inputs: ClassValue[]): string {
  return twMerge(clsx(inputs));
}

export function generateReferralCode(): string {
  const chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789';
  let code = '';
  for (let i = 0; i < 8; i++) {
    code += chars.charAt(Math.floor(Math.random() * chars.length));
  }
  return code;
}

export function formatDate(date: Date | string): string {
  const d = typeof date === 'string' ? new Date(date) : date;
  const now = new Date();
  const diffMs = now.getTime() - d.getTime();
  const diffSeconds = Math.floor(diffMs / 1000);
  const diffMinutes = Math.floor(diffSeconds / 60);
  const diffHours = Math.floor(diffMinutes / 60);
  const diffDays = Math.floor(diffHours / 24);

  if (diffSeconds < 60) return 'just now';
  if (diffMinutes < 60) return `${diffMinutes}m ago`;
  if (diffHours < 24) return `${diffHours}h ago`;
  if (diffDays < 7) return `${diffDays}d ago`;

  return d.toLocaleDateString('en-US', {
    month: 'short',
    day: 'numeric',
    year: d.getFullYear() !== now.getFullYear() ? 'numeric' : undefined,
  });
}

export function formatFullDate(date: Date | string): string {
  const d = typeof date === 'string' ? new Date(date) : date;
  return d.toLocaleDateString('en-US', {
    weekday: 'long',
    year: 'numeric',
    month: 'long',
    day: 'numeric',
  });
}

export async function extractTextFromFile(file: File): Promise<string> {
  const fileType = file.type;
  const fileName = file.name.toLowerCase();

  if (fileType === 'text/plain' || fileName.endsWith('.txt')) {
    return await file.text();
  }

  if (
    fileType === 'application/pdf' ||
    fileName.endsWith('.pdf')
  ) {
    return await extractTextFromPDF(file);
  }

  if (
    fileType ===
      'application/vnd.openxmlformats-officedocument.wordprocessingml.document' ||
    fileName.endsWith('.docx')
  ) {
    return await extractTextFromDOCX(file);
  }

  throw new Error(`Unsupported file type: ${fileType}`);
}

async function extractTextFromPDF(file: File): Promise<string> {
  try {
    const arrayBuffer = await file.arrayBuffer();
    const pdfjsLib = await import('pdfjs-dist');

    pdfjsLib.GlobalWorkerOptions.workerSrc = `//cdnjs.cloudflare.com/ajax/libs/pdf.js/${pdfjsLib.version}/pdf.worker.min.js`;

    const pdf = await pdfjsLib.getDocument({ data: arrayBuffer }).promise;
    let text = '';

    for (let i = 1; i <= pdf.numPages; i++) {
      const page = await pdf.getPage(i);
      const content = await page.getTextContent();
      const pageText = content.items
        .map((item) => ('str' in item ? (item as { str: string }).str : ''))
        .join(' ');
      text += pageText + '\n';
    }

    return text.trim();
  } catch {
    throw new Error('Failed to extract text from PDF. Please try copying and pasting the text directly.');
  }
}

async function extractTextFromDOCX(file: File): Promise<string> {
  try {
    const arrayBuffer = await file.arrayBuffer();
    const mammoth = await import('mammoth');
    const result = await mammoth.extractRawText({ arrayBuffer });
    return result.value.trim();
  } catch {
    throw new Error('Failed to extract text from DOCX. Please try copying and pasting the text directly.');
  }
}

export function scoreColor(score: number): string {
  if (score >= 80) return '#22C55E';
  if (score >= 60) return '#F59E0B';
  if (score >= 40) return '#F97316';
  return '#EF4444';
}

export function getScoreLabel(score: number): string {
  if (score >= 80) return 'Excellent';
  if (score >= 60) return 'Good';
  if (score >= 40) return 'Fair';
  return 'Needs Work';
}

export function truncate(str: string, length: number): string {
  if (str.length <= length) return str;
  return str.slice(0, length) + '...';
}

export function slugify(text: string): string {
  return text
    .toLowerCase()
    .replace(/[^\w\s-]/g, '')
    .replace(/[\s_-]+/g, '-')
    .replace(/^-+|-+$/g, '');
}

export function calculateClientSideScore(
  resumeText: string,
  jobDescription: string
): {
  score: number;
  atsScore: number;
  keywordMatch: number;
  formatQuality: number;
  matchedKeywords: string[];
  missingKeywords: string[];
} {
  const jobWords = jobDescription
    .toLowerCase()
    .split(/\W+/)
    .filter((w) => w.length > 4);

  const resumeLower = resumeText.toLowerCase();

  const uniqueJobWords = Array.from(new Set(jobWords));
  const matchedKeywords = uniqueJobWords.filter((w) => resumeLower.includes(w));
  const missingKeywords = uniqueJobWords
    .filter((w) => !resumeLower.includes(w))
    .slice(0, 10);

  const keywordMatch = Math.round(
    (matchedKeywords.length / Math.max(uniqueJobWords.length, 1)) * 100
  );

  const hasEmail = /[\w.-]+@[\w.-]+\.\w+/.test(resumeText);
  const hasPhone = /[\d\s\-\(\)]{10,}/.test(resumeText);
  const hasBullets = /[•\-*]/.test(resumeText);
  const hasSections =
    /experience|education|skills|summary/i.test(resumeText);
  const hasQuantifications = /\d+%|\$\d+|\d+\+/.test(resumeText);

  const formatChecks = [hasEmail, hasPhone, hasBullets, hasSections, hasQuantifications];
  const formatQuality = Math.round(
    (formatChecks.filter(Boolean).length / formatChecks.length) * 100
  );

  const score = Math.round(keywordMatch * 0.6 + formatQuality * 0.4);

  const atsScore = Math.round(
    (hasSections ? 30 : 0) +
      (hasBullets ? 20 : 0) +
      (hasQuantifications ? 20 : 0) +
      keywordMatch * 0.3
  );

  return {
    score: Math.min(score, 95),
    atsScore: Math.min(atsScore, 95),
    keywordMatch,
    formatQuality,
    matchedKeywords: matchedKeywords.slice(0, 5),
    missingKeywords,
  };
}
