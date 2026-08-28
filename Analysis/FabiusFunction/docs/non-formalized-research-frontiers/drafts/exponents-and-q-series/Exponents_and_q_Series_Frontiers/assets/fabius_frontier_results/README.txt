q-Binomial Richardson Acceleration of Geometric Sinc Products
==============================================================

This archived companion directory preserves the verification code and data
from the former standalone report.  The report itself is now incorporated
into the consolidated source and PDF two levels above this directory.

Files
-----
../../Exponents_and_q_Series_Frontiers.tex   Consolidated LaTeX source.
../../Exponents_and_q_Series_Frontiers.pdf   Consolidated rendered report.
verify_frontier_results.py                   Symbolic and high-precision numerical checks.
numerical_results.txt                        Human-readable verification output.
numerical_results.csv                        Machine-readable error table.

Reproduce the computations
--------------------------
python verify_frontier_results.py

The script requires Python 3, mpmath, and SymPy. It uses no network access.

Compile the report
------------------
Run from this companion directory:

cd ../..
pdflatex -interaction=nonstopmode -halt-on-error Exponents_and_q_Series_Frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error Exponents_and_q_Series_Frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error Exponents_and_q_Series_Frontiers.tex

The report was compiled with pdfLaTeX. It uses standard TeX Live packages and
Libertinus when available, with Latin Modern as its explicit fallback.

Scope and status
----------------
The former report's theorems are preserved in the consolidated LaTeX source
and numerically checked by the script. The denominator-free finite q-binomial,
principal-specialization, scaled exact-row, and all-positive-moment algebra is
formalized in Lean. For rational 0 < q < 1, the finite Lagrange weights, all
residual moments and their signs, the exact finite l1 norm, and q=1/4
specializations also have Lean counterparts. The generic and reconciled
rational layers are recorded at source checkpoints
1e761ed77583e9870ceeaeb2c74ac824094f0f3f and
f77ff7c296b99050107948f5aa2a9488aec01d05, respectively. The
analytic sinc-tail acceleration, transformed error and remainder, spline,
inverse, and infinite-limit claims remain research frontiers. "Repository-new"
means absent from the audited *.tex corpus under the
stated ProveIt repository path; it is not an unconditional claim of priority
over all external literature.
