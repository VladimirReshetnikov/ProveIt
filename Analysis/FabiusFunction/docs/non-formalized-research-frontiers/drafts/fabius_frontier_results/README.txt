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
latexmk -pdf q_richardson_sinc_frontier.tex

The report was compiled with pdfLaTeX. It uses standard TeX Live packages and
Latin Modern fonts.

Scope and status
----------------
The report's theorems are proved in the LaTeX source and numerically checked by
the script. They have not yet been formalized in Lean. "Repository-new" means
absent from the audited *.tex corpus under the stated ProveIt repository path;
it is not an unconditional claim of priority over all external literature.
