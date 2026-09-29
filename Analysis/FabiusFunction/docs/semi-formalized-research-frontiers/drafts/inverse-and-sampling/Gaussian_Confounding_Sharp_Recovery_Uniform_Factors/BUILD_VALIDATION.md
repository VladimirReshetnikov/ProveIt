# Build and validation record

Validation date: 29 September 2026.

## PDF

- Three successful `pdflatex -interaction=nonstopmode -halt-on-error` passes.
- Final pass: no LaTeX warnings, undefined references, or overfull/underfull boxes.
- Output: 19 A4 pages; no encryption; 83 link annotations.
- Every page rendered with Poppler `pdftoppm` (1000-pixel maximum side).
- All 19 rendered pages inspected in three contact sheets; the main likelihood
  theorem and proof page was additionally inspected as an individual page.
- No observed clipping, overlapping text, missing-glyph squares, or broken tables.
- Programmatic text check: no replacement characters, unresolved `??` markers,
  or text words outside a generous 15-point page margin.
- The source contains one complete document and an embedded bibliography.

Rendering and text checks establish presentation integrity, not mathematical
correctness. Scratch renders, LaTeX auxiliary files, and local font files are
not part of the delivered archive. PDF metadata makes byte-identical rebuilds
unnecessary; the supplied checksum identifies the delivered PDF itself.

## Supporting calculations

The supporting program was run successfully again after completing the article.
Environment: Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0.

- 7,000 exact rational shifted-moment inequality checks passed.
- 40 exact moment-tangent checks passed.
- Eight exact polynomial flows and rational all-positive-root certificates passed.
- Exact two-factor density and chi-square leading coefficients passed.
- Five 80-digit Fourier diagnostics were produced.

The numerical diagnostics are not rigorous interval enclosures. No statistical
sampling experiment or computational minimax proof is claimed. Full mathematical
claims rest on the proofs in the article and remain unrefereed and not
proof-assistant-checked.

Machine-readable presentation metadata is in `artifacts/build_validation.json`;
calculation records are in `artifacts/verification_results.json`.
