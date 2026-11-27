# Build and visual verification

The delivered manuscript was compiled from `report.tex` using pdfTeX
1.40.26 (TeX Live 2025/dev/Debian), LaTeX2e 2024-11-01 patch level 2, and
BibTeX 0.99d. It has 22 A4 pages with embedded Latin Modern, AMS, and figure
fonts.

The container had the TeX sources and fonts but lacked generated filename
databases and a usable default format. For this build, a fresh pdfLaTeX
format was generated from the installed LaTeX source in a temporary,
task-local directory. Explicit resource paths and a local font map were
used. No source theorem or report content was changed for this repair.
On a normally configured TeX installation, the standard `make pdf` command
in the README suffices; no special runtime files are required by the paper.

BibTeX and repeated pdfLaTeX passes resolved all references. The final log
contains zero LaTeX warnings, zero overfull boxes, and zero underfull boxes.
The PDF was rendered page by page at 95 dpi. The first half, including the
main theorem, valuation proof, and cubic example figure, was visually
checked by the coordinating agent. A separate agent visually checked
physical pages 12–22, including the branch results, tables, second figure,
formalization appendix, and bibliography. All pages passed the layout
review; no clipping, overlap, broken references, or unreadable equations
were observed.

The PDF and archive were checked after compilation. This visual/build
verification concerns the new manuscript. It is not a Lean build of the
upstream proof.
