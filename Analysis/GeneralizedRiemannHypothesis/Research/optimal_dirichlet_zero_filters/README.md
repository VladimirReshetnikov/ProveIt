# Optimal positive filters for clusters of Dirichlet zero frequencies

Research note, 2026-11-27. The PDF and TeX are the primary deliverables. The extremal theorems are unconditional; the application to prime errors uses the Dirichlet GRH theorem reported in the vendored Lean project. No Lean build or formal verification was performed in this session, and no global literature-priority claim is made.

## Files
- `optimal_zero_filters.tex`, `optimal_zero_filters.pdf`: full proofs, source analysis, applications, references and further questions.
- `check_filters.py`: exact symbolic polynomial checks and high-precision numerical illustrations (not part of the proof).
- `checks.json`: output of running the script.
- `source_audit.md`: inspected GitHub source locations and retrieved blob SHAs.

## Reproduction
Run `pdflatex -halt-on-error optimal_zero_filters.tex` twice. Run `python check_filters.py > checks.json` with Python 3, SymPy and mpmath installed. The numeric solutions are illustrative; the general analytic-deformation theorem has an existential, not a certified quantitative, neighborhood.
