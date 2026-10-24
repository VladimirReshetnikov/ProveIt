# Report quality-assurance receipt

Status: PASS. Reviewed 2026-10-24T22:59:53.676262+00:00.

- The final PDF has 17 pages. All pages were rendered at 150 dpi and individually inspected. No overflow, clipping, missing glyph, collision, unreadable formula or orphan heading was observed.
- Two pdfLaTeX passes completed with zero warnings, overfull boxes or underfull boxes. All 17 fonts are embedded and Unicode mapped. Text-bound checks pass on all pages.
- All 72 inherited mathematical display blocks match after only declared typography and local-argument alpha-renaming. Seven added twelve-variable prefix identities match its literal specification. The report-only checker passes identically under normal and optimized Python.
- The report uses isolated section copies. Every original producer section retains its source hash. Late paired-sign attribution and the precise inherited-calibration boundary are explicit.
- The literal command `build.py --check` was verified by PDF text extraction, avoiding the TeX en-dash ligature.

Final PDF SHA-256: `3875b292c19921d83774644003107254e0b8b3f0198917c86748844f3dbffa0e`.

Main TeX SHA-256: `fe815a048dc1325e8325896c847a765d79a673c50e317ff331c1ee3ed4634d82`.

Complete source, build-script, PDF and audit hashes, with per-page render evidence, are in `QA_RECEIPT.json`. The render files and build intermediates need not be distributed. Any later source or PDF change requires updated hashes and visual verification.

This is editorial and transcription QA, not an independent end-to-end proof of the inherited source/calculus calibration. The component mathematical audits and stated theorem interfaces retain their own scope.
