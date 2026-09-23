# Build and verification report

## Document

- Source: `omnific_small_quotients.tex`.
- Output: `omnific_small_quotients.pdf`.
- PDF length: 26 physical pages (title; one-page linked contents; 24 numbered pages).
- Engine: pdfLaTeX, via latexmk.
- Build command: `latexmk -pdf -interaction=nonstopmode -halt-on-error omnific_small_quotients.tex`.
- Final build: successful, with no undefined references/citations, overfull or
  underfull box warnings, duplicate PDF destinations, or LaTeX warnings found
  in the final log.
- Pages rendered for inspection; overview sheets and selected full-size pages
  checked, including the cover, contents, main collision proof, finite-coordinate
  invariant, and bibliography.
- No external figures, custom fonts, or bibliography data files are needed.

## Finite algebra

`python finite_checks.py` completed successfully:

- 320 finite telescoping identities, with positive witness supports.
- 300 constant-coefficient multiplication checks.
- 600 coordinate Hahn Leibniz identities.
- 19 binomial m-th-power identities through order 20.
- 9 diagonal derivation tests.
- 29 nonzero first negative root-correction checks.

Total: **1,277 exact finite test cases**. All arithmetic uses rational numbers
from Python's `fractions.Fraction`, with deterministic seed 20260922.

These tests do not prove the infinite or class-sized theorems. The manuscript
contains their mathematical proofs, but no proof-assistant or independent
review certificate is included or claimed.
