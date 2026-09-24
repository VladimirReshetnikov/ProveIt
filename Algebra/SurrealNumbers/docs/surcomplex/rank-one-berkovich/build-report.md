# Build and verification report

## LaTeX

- Engine: pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian).
- Build driver: latexmk 4.86.
- Command: `latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex`.
- Output: **30 pages**.
- Final log: no LaTeX errors, unresolved references or citations, LaTeX/package warnings, overfull boxes, or underfull boxes.
- Bibliography and two diagrams are embedded in the source.
- External PDF links were inspected programmatically; repository links use the pinned commit.

## Rendering and layout

The document was rendered with PyMuPDF and Poppler (`pdftoppm` 25.06.0). Page contact sheets and enlarged mathematical-diagram pages were visually inspected. A text bounding-box scan found no text outside the specified page safety boundaries. The figures were revised to remove label/line interference before the final build.

## Finite computations

`verify_examples.py` executed under Python 3.13.5, using only standard-library exact rational arithmetic: **542/542 assertions passed**. Full results are in `verification.json`.

These are artifact and finite-computation checks, not a formal verification or an independent mathematical referee report.
