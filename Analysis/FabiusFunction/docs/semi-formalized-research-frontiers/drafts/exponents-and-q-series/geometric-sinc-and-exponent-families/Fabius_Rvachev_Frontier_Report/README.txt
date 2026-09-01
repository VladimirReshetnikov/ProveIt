Negative Parameters, Reciprocal Bases, and the Gaussian Boundary
=================================================================

Files
-----
fabius_frontier_report.tex   LaTeX source
fabius_frontier_report.pdf   compiled report
numerical_experiments.py     reproducible numerical experiments
numerical_results.tex        generated LaTeX tables
*.csv                        machine-readable numerical results
figures/*.pdf, *.png         report figures

Reproduce the numerical experiments
-----------------------------------
python numerical_experiments.py

Required Python packages: numpy, scipy, matplotlib.
The script uses a fixed random seed (20260830) and deterministic truncation bounds.

Compile the report
------------------
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex

The repository copy selects Libertinus when available, falling back to Latin
Modern only on hosts without the package.  Its committed PDF was rebuilt with
Libertinus and uses the supplied PNG figure companions to avoid Type-3 fonts.
The current 1,475-line source matches the 809,516-byte, 26-page A4 PDF.  All 22
font rows are embedded and subset, including five Libertinus rows, with no
Type-3 font; the active 13-entry checksum ledger verifies in full.

The report treats novelty as novelty relative to the inspected ProveIt repository
corpus as of 30 August 2026; it does not assert global publication priority.
