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
latexmk -pdf -interaction=nonstopmode -halt-on-error fabius_frontier_report.tex

The report treats novelty as novelty relative to the inspected ProveIt repository
corpus as of 30 August 2026; it does not assert global publication priority.
