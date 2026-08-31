# Validation record

- LaTeX engine: pdfTeX 1.40.26 through `latexmk` 4.86 (TeX Live 2025/dev).
- Final PDF: 30 A4 pages, unencrypted, no forms or JavaScript.
- Final LaTeX log: no errors, unresolved references/citations, package
  warnings, overfull boxes, or underfull boxes.
- Fonts: all embedded; no Type-3 fonts in the report or generated vector plots.
- Visual preflight: all 30 pages rendered at 170 dpi and inspected in contact
  sheets; full-resolution spot checks covered the title/abstract, dense
  theorem/plot pages, numerical table and command listing, and bibliography.
  No clipping, overlap, missing glyphs, or broken figures was found.
- Python: `frontier_experiments.py` passes byte-code compilation.
- Exact reproducibility: all deterministic CSV/TXT/TeX certificate outputs
  reproduced byte-for-byte in a fresh output directory.
- Largest multiprecision differential-operator residual in the shipped test
  table: `8.37792516211e-122`.
- Golden-ratio recurrence evidence: checked exactly through level 25; the
  manuscript keeps it conjectural.
