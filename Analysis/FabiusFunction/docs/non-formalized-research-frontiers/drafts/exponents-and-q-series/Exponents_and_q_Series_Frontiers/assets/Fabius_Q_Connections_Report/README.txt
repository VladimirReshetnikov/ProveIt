BEYOND THE DYADIC FABIUS WEB
============================

Contents
--------
- fabius_q_connections_report.pdf : compiled 29-page research report
- fabius_q_connections_report.tex : complete LaTeX source
- q_fabius_experiments.py         : deterministic numerical verification code
- numerics/                       : residual tables, q-Lagrange weights, cumulants
- figures/                        : vector PDF and PNG versions of the report figures
- SHA256SUMS.txt                  : integrity hashes for every packaged file

Compilation
-----------
The report was compiled with LuaLaTeX. From this directory, run:

    lualatex fabius_q_connections_report.tex
    lualatex fabius_q_connections_report.tex
    lualatex fabius_q_connections_report.tex

Numerical reproduction
----------------------
Python 3 with NumPy, mpmath, and Matplotlib is required. Run:

    python q_fabius_experiments.py

The program writes its generated tables and figures to its selected output
directory. It contains detailed comments explaining every experiment and the
identities tested.

Status labels used in the report
--------------------------------
The report distinguishes proved theorems, computational observations, and
explicitly labeled conjectures. Claims of novelty are relative to the audited
ProveIt Fabius-function LaTeX corpus and the cited literature, not an assertion
of exhaustive priority across all unpublished work.
