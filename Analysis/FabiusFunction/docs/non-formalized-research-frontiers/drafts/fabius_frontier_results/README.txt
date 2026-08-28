q-Binomial Richardson Acceleration of Geometric Sinc Products
==============================================================

Files
-----
q_richardson_sinc_frontier.tex   Main LaTeX report.
q_richardson_sinc_frontier.pdf   Rendered report.
verify_frontier_results.py       Symbolic and high-precision numerical checks.
numerical_results.txt            Human-readable output from the verification script.
numerical_results.csv            Machine-readable error table.

Reproduce the computations
--------------------------
python verify_frontier_results.py

The script requires Python 3, mpmath, and SymPy. It uses no network access.

Compile the report
------------------
pdflatex -interaction=nonstopmode -halt-on-error q_richardson_sinc_frontier.tex
pdflatex -interaction=nonstopmode -halt-on-error q_richardson_sinc_frontier.tex
pdflatex -interaction=nonstopmode -halt-on-error q_richardson_sinc_frontier.tex

The report was compiled with pdfLaTeX. It uses standard TeX Live packages and
Libertinus when available, with Latin Modern as its explicit fallback.

Scope and status
----------------
The report's theorems are proved in the LaTeX source and numerically checked by
the script. The denominator-free finite q-binomial, geometric Lagrange-weight,
principal-specialization, and all-positive-moment algebra is now formalized in
Lean, with the post-snapshot boundary recorded at source checkpoint
1e761ed77583e9870ceeaeb2c74ac824094f0f3f. The analytic sinc-product error,
positivity, stability, spline, and inverse-function consequences remain
research frontiers. "Repository-new" means absent from the audited *.tex corpus
under the stated ProveIt repository path; it is not an unconditional claim of
priority over all external literature.
