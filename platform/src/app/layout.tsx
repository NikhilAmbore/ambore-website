import React from 'react';
import type { Metadata } from 'next';
import { Inter } from 'next/font/google';
import './globals.css';
import PostHogProvider from '@/components/providers/PostHogProvider';
import SessionProvider from '@/components/providers/SessionProvider';
import { Toaster } from 'react-hot-toast';

const inter = Inter({
  subsets: ['latin'],
  display: 'swap',
  variable: '--font-inter',
});

export const metadata: Metadata = {
  metadataBase: new URL(process.env.NEXT_PUBLIC_APP_URL ?? 'https://ambore.io'),
  title: {
    default: 'Ambore – AI Career Platform',
    template: '%s | Ambore',
  },
  description:
    'Check how well your resume matches any job instantly. Get your ATS score, missing keywords, and an AI-optimized resume in 60 seconds. Free forever.',
  keywords: [
    'resume analyzer',
    'ATS score',
    'AI resume',
    'career platform',
    'job matching',
    'resume optimization',
    'interview prep',
  ],
  authors: [{ name: 'Ambore' }],
  creator: 'Ambore',
  publisher: 'Ambore',
  openGraph: {
    type: 'website',
    locale: 'en_US',
    url: process.env.NEXT_PUBLIC_APP_URL ?? 'https://ambore.io',
    siteName: 'Ambore – AI Career Platform',
    title: 'Ambore – AI Career Platform',
    description:
      'Check how well your resume matches any job instantly. Get ATS score, missing keywords, and AI-optimized resume in 60 seconds.',
    images: [
      {
        url: '/og-image.png',
        width: 1200,
        height: 630,
        alt: 'Ambore – AI Career Platform',
      },
    ],
  },
  twitter: {
    card: 'summary_large_image',
    title: 'Ambore – AI Career Platform',
    description:
      'Check how well your resume matches any job instantly. Free ATS score + AI optimization.',
    images: ['/og-image.png'],
    creator: '@ambore_io',
  },
  robots: {
    index: true,
    follow: true,
    googleBot: {
      index: true,
      follow: true,
      'max-video-preview': -1,
      'max-image-preview': 'large',
      'max-snippet': -1,
    },
  },
  icons: {
    icon: '/favicon.ico',
    shortcut: '/favicon-16x16.png',
    apple: '/apple-touch-icon.png',
  },
  manifest: '/site.webmanifest',
};

const jsonLd = {
  '@context': 'https://schema.org',
  '@type': 'SoftwareApplication',
  name: 'Ambore – AI Career Platform',
  applicationCategory: 'BusinessApplication',
  operatingSystem: 'Web',
  description:
    'AI-powered career platform to analyze resumes, match jobs, and optimize your application for ATS systems.',
  offers: {
    '@type': 'Offer',
    price: '0',
    priceCurrency: 'USD',
  },
  aggregateRating: {
    '@type': 'AggregateRating',
    ratingValue: '4.9',
    reviewCount: '2840',
  },
};

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en" className={inter.variable}>
      <head>
        <meta charSet="utf-8" />
        <meta name="viewport" content="width=device-width, initial-scale=1" />
        <link rel="canonical" href={process.env.NEXT_PUBLIC_APP_URL ?? 'https://ambore.io'} />
        <script
          type="application/ld+json"
          dangerouslySetInnerHTML={{ __html: JSON.stringify(jsonLd) }}
        />
      </head>
      <body className="bg-[#09090B] text-[#F8FAFC] font-sans antialiased">
        <SessionProvider session={null}>
          <PostHogProvider>
            {children}
            <Toaster
              position="top-right"
              toastOptions={{
                duration: 4000,
                style: {
                  background: '#1C1C1E',
                  color: '#F8FAFC',
                  border: '1px solid rgba(255,255,255,0.1)',
                  borderRadius: '8px',
                },
                success: { iconTheme: { primary: '#22C55E', secondary: '#1C1C1E' } },
                error: { iconTheme: { primary: '#EF4444', secondary: '#1C1C1E' } },
              }}
            />
          </PostHogProvider>
        </SessionProvider>
      </body>
    </html>
  );
}
