# Validation record

- LaTeX engine: pdfTeX 1.40.22 (TeX Live 2022/dev); exactly three clean,
  strict, serial direct `pdflatex` passes.
- Final PDF: 30 A4 pages, unencrypted, no forms or JavaScript.
- Final LaTeX log: no errors, unresolved references/citations, package
  warnings, overfull boxes, or underfull boxes.
- Fonts: all 30 report font rows are embedded and subset; six are Libertinus;
  none is Type 3. The manuscript selects the retained PNG plot companions.
- Render preflight: all 30 A4, rotation-zero pages rendered successfully and
  contained extractable non-whitespace text.
- Python: `frontier_experiments.py` passes byte-code compilation.
- Exact reproducibility: all deterministic CSV/TXT/TeX certificate outputs
  reproduced byte-for-byte in a fresh output directory.
- Largest multiprecision differential-operator residual in the shipped test
  table: `8.37792516211e-122`.
- Golden-ratio recurrence evidence: checked exactly through level 25; the
  manuscript keeps it conjectural.
