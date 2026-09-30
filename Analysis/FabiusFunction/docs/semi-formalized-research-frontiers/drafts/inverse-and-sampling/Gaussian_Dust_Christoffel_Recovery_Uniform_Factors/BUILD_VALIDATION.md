# Build and validation record

## Final PDF

- File: `article.pdf`; 22 pages; 611,147 bytes.
- Source: standalone `article.tex`, with embedded bibliography and table.
- Compiler: pdfTeX 3.141592653-2.6-1.40.26, TeX Live 2025/dev/Debian.
- Three successful final pdfLaTeX passes with `-interaction=nonstopmode -halt-on-error`.
- No overfull boxes, undefined citations/references, rerun requests, or LaTeX errors.
- Four underfull horizontal-box warnings remain in a summary table and long
  bibliography paragraphs; the corresponding layouts were inspected.

All 22 final pages were rendered with MuPDF and inspected in a contact sheet.
The title, the dyadic formula/table, and the final bibliography page were also
inspected at full-page resolution. The title and dyadic page were rendered again
with Poppler `pdftoppm` 25.06.0; the dyadic page was visually checked in that
independent renderer. No clipping, overlapping equations, black replacement
squares, or visibly broken glyphs were found. A programmatic text-span check
found no spans outside any page; extracted text contains no Unicode replacement
characters or unresolved double-question-mark references.

Rendering images and TeX build intermediates are not part of the deliverable.
No font files or copies of third-party source articles are distributed.

## Executed verification

`python verify_results.py` was rerun on the final payload. All 4,619 exact checks
and three 90-digit Fourier diagnostics passed. Category counts and software
versions are in `artifacts/verification_results.json`.

The exact checks cover uniform cumulants; local Taylor constants; rational
Cauchy determinants and geometric Schur complements; finite moment ladders;
tail inequalities; finite Christoffel termination and monotonicity; and
coefficient-error bounds. The numerical checks concern characteristic functions,
not total-variation quadrature, and are not interval certificates.

## Mathematical boundary

These are conventional mathematical proofs developed for the assumptions in
the article. No independent referee review or Lean/Rocq verification has been
performed. Finite checks do not prove infinite-dimensional theorems. The
statistical envelope rates are upper bounds, not established minimax optima.
Literature attribution and the limits of the repository comparison appear in
`SOURCE_AUDIT.md`; result-by-result scope is in `CLAIM_LEDGER.md`.

## Archive integrity

`SHA256SUMS.txt` records every distributed payload file except itself. The ZIP
was checked for archive integrity and includes one top-level directory. Its
source and PDF are the same files offered as individual downloads.
