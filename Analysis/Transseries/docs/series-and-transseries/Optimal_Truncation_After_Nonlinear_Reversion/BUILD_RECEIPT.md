# Build and verification receipt

Date: 29 September 2026.

## PDF

The supplied `article.pdf` was rebuilt from the supplied `article.tex` using
`build.sh`: three successful pdflatex passes. The result has 22 A4 pages.
The final LaTeX log reported no errors, undefined references/citations,
overfull boxes, or underfull boxes.

All pages were rendered with Poppler at 90 dpi and inspected in contact sheets.
The title page and a dense mathematical page were additionally inspected at
140 dpi; the final bibliography was inspected at 110 dpi. An all-page text-box
check found no text spans outside page boundaries and no replacement-character
markers in extracted text. These are presentation checks, not mathematical
formal verification.

## Exact and symbolic checks

- `exact_checks.py`: the formal inverse residual vanishes in all 13 coefficients
  through degree 12. Six exact-rational shifted-digamma sign/enclosure checks
  passed, for direct partial sums and their midpoints at X=3, 5, and 8.
- `derive_coefficients.py`: the symbolic assertions for B1, D1, D2, theta1,
  theta2, and the second cutoff coefficient passed.

## High-precision checks

`verify.py --max-order 240 --output results.csv` ran at 312 decimal digits and
computed through inverse coefficient 241. The recorded run covers eight cases:
five growing orders at sigma=3/4 and three additional offsets at M=240.
All executed assertions passed. The CSV includes raw scaled residuals, not just
rounded agreement claims. These calculations are not outward-rounded intervals.

## Boundaries

The analytic theorems are conventional proofs in the article. No Lean
formalization, independent refereeing, exhaustive novelty search, or repository
write was performed. Exact rational certificates rely on the analytic identities
and derivative bounds proved in the article.
