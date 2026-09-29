# Build and inspection record

Date: 29 September 2026.

## Artifact

- PDF: 24 A4 pages, 387,964 bytes.
- Editable source: `article.tex`; figure source and numerical data included.
- Eight numbered theorems, supplementary lemmas/propositions/corollaries,
  two appendices, and ten proposed research questions.
- Python: 3.13.5; matplotlib: 3.10.8.
- SymPy and mpmath versions are recorded in `results/verification.json`.

## Executed checks

- `python verify.py --out results`: PASS.
- `python make_figure.py`: completed; 363 plotted numerical data points.
- Three successive pdfLaTeX passes: completed.
- Final LaTeX log: no overfull boxes, no underfull boxes, no LaTeX warnings,
  no undefined references, and no multiply defined labels.
- Extracted PDF text: no unresolved `??` reference markers.
- All PDF text blocks lie within their page boundaries.
- All pages rendered with Poppler and visually inspected in page contact
  sheets. The numerical/figure and end-matter pages were re-rendered and
  inspected after adjusting float placement and heading pagination.
- The figure, tables, mathematical displays, and bibliography were checked
  for visible clipping and layout collisions; none were observed.

## Boundaries of this record

This is a reproducibility and layout record, not independent peer review.
The proofs are not Lean formalizations. Numerical evaluations use arbitrary
precision but not interval arithmetic. Mathematical novelty and priority have
not been established by an exhaustive literature search. The manuscript
states its imported results, hypotheses, and unresolved extensions explicitly.
