# Verification summary

The article was checked on 2 October 2026. It contains 14 pages.

## Mathematical checks

The integrated article received a fresh mathematical review after the separate central and rare-tail derivations were reviewed. Explicit central, diagonal, quantile and rare-tail coefficients were independently rederived, and the uniform remainder arguments and interpolation/rounding caveats were checked. The only requested integration clarification was to specify the local nonvanishing domain and continuous branch for the central logarithm. The final article includes it, and uses the characteristic function directly in the global rare-tail Fourier integral.

Reviewed TeX SHA-256: `df1e8c2d837ec98ddaafb74c47c64b24b08a8b1e068f40a26ebffc56c0a4736d`

This is ordinary mathematical review, not formal proof-assistant certification. Source searches support bounded novelty statements only.

## Reproducible checks

The included replay asserts agreement of:

- P1 through P4 from the cumulant construction and an independent raw-moment logarithm calculation
- The diagonal coefficients through order 7, including vanishing even powers
- Diagonal counts through n=5 from exact simplex arithmetic and independent direct word counting
- All 20 rectangular direct-count/simplex comparisons for m=1,...,4 and k=1,...,5
- Both displayed inverse-probability corrections
- The saddle displacement, transform corrections and first rare-tail coefficient
- Exact rare-tail probabilities from two distinct polynomial algorithms
- Regenerated JSON outputs and the archived baselines

Finite numerical diagnostics are explicitly distinguished from the analytic asymptotic proofs.

## PDF and package checks

All 14 rendered pages were visually inspected. The final build has no overfull or underfull box warnings and no undefined references. The contents fits the first page, the long repository hash does not overflow, the command-line flag uses two literal hyphens, and the bibliography stays together on the final page.

The release process verifies the explicit file list, manifest hashes, absence of symlinks and unsafe archive paths, then tests Python zipfile extraction followed by `bash replay.sh --with-pdf` without executable bits. The archive excludes external full papers, temporary build files, page renders and working review reports. Rebuilt PDFs may differ in embedded timestamp bytes; the pinned source and baseline PDF are separately hashed.
