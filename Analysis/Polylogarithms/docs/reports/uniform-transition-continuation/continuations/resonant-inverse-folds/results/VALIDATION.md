# Validation record

The supplied package contains 17 named theorems, propositions, and corollaries
with conventional proofs, in a 21-page A4 PDF. Not all are novelty claims:
classical consequences and classical methods are identified separately.

## Executed mathematical replays

- `verify_exact.py`: 150 exact assertions passed, SymPy 1.14.0.
- `verify_numeric.py --dps 180`: 73 diagnostics passed, mpmath 1.3.0.
- Runtime used: Python 3.13.5.

The receipts record individual scopes, tolerances, and residuals. They are
not proof-assistant coverage and the numerical values are not interval
certificates. The low-precision guard was separately smoke-tested: a
120-digit request exits with a message requiring 180 digits for the fixed
tolerances. The table-only output formatting was replayed successfully.

## PDF checks

The final source compiled with three pdfLaTeX passes. There were no LaTeX
warnings, unresolved references, or overfull/underfull boxes. The extracted
PDF text contains no unresolved `??` markers and no text blocks outside the
page bounds.

All 21 final pages were rendered at 120 dpi and reviewed as page montages;
pages 9, 14, and 17 were additionally inspected at full rendered size.
No clipping, overlaps, missing mathematical glyphs, or table truncation was
observed. The title and contents each occupy a dedicated page.

The result dependency ledger includes the compiled statement numbers and
starting pages. `validation.json` contains the machine-readable record.
