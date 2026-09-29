# Delivery validation

Validated September 29, 2026.

## Document

- PDF: 26 pages, US Letter, unencrypted, selectable text.
- Compiled with pdfTeX 1.40.26 (TeX Live 2025).
- Final compilation has no undefined or duplicate labels/citations,
  no LaTeX/package warnings, and no overfull or underfull boxes.
- All references in the source were checked against defined labels.
- All PDF pages were rendered and visually reviewed in page montages.
  Representative title, proof, and table pages were also rendered at
  higher resolution. No clipping, overlap, missing glyphs, or black
  replacement boxes were observed.
- All document and figure fonts are embedded. No standalone font files
  are distributed.
- The supplied build.sh was executed successfully. It keeps auxiliary
  files in a temporary directory and copies back only article.pdf.

## Core finite tests

Python 3.13.5; standard library only; recorded result PASS.
31 independent clipping-coefficient comparisons, 40 probability
coefficients, exact median 9, direct brute-force comparison through n=8,
2,055 avoiding permutations, 804 skeletons of costs 2--7, and 269,402
reconstruction/injectivity tests within the specified finite ranges.

## Optional symbolic tests

SymPy 1.14.0; recorded result PASS.
Six singular expansion coefficients, equality of radical and state-derived
probability generating functions, the algebraic certificate, and the
second-order probability and survival constants were checked exactly.

## Data and figures

Rational probability coefficients through k=256 and exact finite
histograms through n=12 were generated. The two figures were regenerated
with Matplotlib 3.10.8 from the retained CSV data. Decimal displays and
plots are illustrative, not interval certificates.

## Mathematical status

Written proofs and finite checks, not proof-assistant verification or
external peer review. The precise limits of the claims are documented
in PROOF_STATUS.md and the article's audit section. No GitHub files were
modified or uploaded.
