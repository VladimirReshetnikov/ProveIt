# Build and verification record

- pdfLaTeX compilation: two successful passes, final log contains no overfull/underfull box warnings or LaTeX warnings.
- PDF: 10 letter-size pages, rendered using the PDF skill renderer and inspected as a page montage. No visible clipping, overlaps or missing glyphs.
- `checks/verify.py`: passed. 8 levels, 124 local-bin cases, 108 coverage checks, 6,318 saturation checks; the largest synthetic height has 244 digits. Four finite near-lattice interpolation systems also passed the coefficient, column-norm, residual and sampled positivity tests.
- `checks/allocate.py`: passed the exact-rational tagged-occurrence conservation and class-geometry assertions; its small illustrative parameters intentionally leave four residual items. It is not an instance of the asymptotic parameter theorem.
- The numerical tests are regression diagnostics, not proofs of the count envelope, asymptotic theorem or exact Fourier identities. The proof is in `paper.tex`.
- No Lean build, peer review, or exhaustive literature search was performed.
