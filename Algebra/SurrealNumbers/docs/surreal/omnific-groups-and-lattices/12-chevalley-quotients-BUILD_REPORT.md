# Build and inspection report

## PDF build

- Engine: pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian).
- Build command: `latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex`.
- Physical page count: 28 (title page, contents page, and 26 numbered article pages).
- Page size: US Letter, 612 by 792 PDF points.
- Final build: no LaTeX warnings, unresolved references, duplicate page destinations, or overfull/underfull boxes.
- Theorem, lemma, proposition, and corollary references use the corresponding names.
- Approximately 11,948 words in extracted PDF text; mathematical extraction is not a semantic verification method.

## Layout checks

All pages were rendered with Poppler at 90 dpi and inspected in contact sheets. The title, root-kernel proof, Lie proof, dependency display, and explicit G2 matrices were also rendered at higher resolution for spot inspection. Automated text-block checks found no content outside a conservative safe page boundary. No unresolved double-question-mark reference placeholders were found.

The final PDF and source were checked again after reference-label corrections. This is a layout and build review, not independent mathematical refereeing.

## Exact finite verification

The recorded run of `verify.py` passed 2,188 checks using Python 3.13.5 and SymPy 1.14.0. Detailed counts and root-system coverage are in `verification_results.json`.

The verifier's scope is finite symbolic and exact arithmetic. No theorem about arbitrary normal-form supports, arbitrary class maps, or all group homomorphisms was machine-verified. No Lean build or new Lean formalization is part of this package.

## Package

The source is self-contained, with an internal bibliography and no external figures. No font files are included. The archive omits intermediate TeX auxiliary files and exploratory scripts. SHA256SUMS.txt records hashes of the final deliverables other than itself.
