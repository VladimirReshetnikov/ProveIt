Closed All-Orders Endpoint Asymptotics for the Inverse Fabius Function
======================================================================

Contents
--------
inverse_fabius_all_orders.tex
    LaTeX source of the 27-page research report.

inverse_fabius_all_orders.pdf
    Compiled report.

inverse_fabius_asymptotics.py
    Commented reproducibility program. It performs exact rational dyadic
    tests, high-precision Gamma-zeta Fourier evaluation, and exact symbolic
    checks of the diagonal Lagrange-Buermann coefficient formula.

results/endpoint_errors.csv
    Full-precision relative-error table.

results/endpoint_error_plot.pdf
results/endpoint_error_plot.png
    Vector and raster error plots.

results/constants.txt
    Constants and the first Fourier coefficient at 100-digit precision.

results/symbolic_checks.txt
    Exact SymPy verification log.

Reproduce the computations
--------------------------
From this directory, run:

  python inverse_fabius_asymptotics.py --output-dir results \
      --precision 100 --modes 12 --depths 5 10 20 40 80 120 160

Dependencies: Python 3.10+, mpmath, sympy, matplotlib.
No network access is used by the script.

Compile the report
------------------
A standard pdflatex/latexmk installation with the packages named in the
preamble is sufficient. The figure path is relative to this directory:
results/endpoint_error_plot.png.

Source corpus
-------------
The report audits the LaTeX corpus under:
https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/FabiusFunction/docs
(including subdirectories), as accessed on 28 August 2026.

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Inverse_Endpoint_All_Orders.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.
