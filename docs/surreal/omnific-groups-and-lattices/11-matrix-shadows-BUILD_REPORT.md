# Build and verification report

## Article build

- Source: `omnific_matrix_groups.tex`.
- Engine: pdfLaTeX, driven by latexmk.
- Result: successful compilation, 24 PDF pages, US Letter.
- Final LaTeX log: no undefined references, no undefined citations, no
  overfull or underfull box warnings.
- Bibliography is inline; no separate BibTeX step is required.

## Finite algebra checks

- Program: `verify.py` (Python standard library only).
- Result: PASS, 2,111 exact checks.
- Detailed family counts: `verification_results.json`.
- Scope: finite polynomial/matrix identities and geometric-series truncation
  remainders. These checks do not certify the infinite or class-level proofs.

## PDF review

The PDF was rendered with MuPDF. All pages were checked in a contact sheet and
representative pages were inspected at higher resolution, including the title,
root-kernel proof, small-support cardinal arguments, and bibliography. A
programmatic span-boundary check found no text outside the checked page bounds.
The final version uses a one-page contents/reading guide and a separate
bibliography page to avoid an almost-empty continuation contents page or a
bibliography entry beginning at the bottom of the preceding page.

This is a rendering/build report, not a mathematical correctness certificate.
No third-party font files or repository source files are distributed.
