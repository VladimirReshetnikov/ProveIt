FINITE DYADIC SINC PRODUCTS AND RVACHEV UP APPROXIMANTS
=======================================================

Main files
----------
finite_sinc_products_report.tex   Complete LaTeX source.
finite_sinc_products_report.pdf   Compiled 22-page report.
finite_sinc_experiments.py        Reproducible numerical and exact-arithmetic code.

Generated figures
-----------------
finite_sinc_approximants.pdf
scaled_error_profiles.pdf
convergence_comparison.pdf

Generated data
--------------
sharp_error_verification.csv
positive_acceleration_verification.csv
exact_coefficients.txt
exact_rational_samples.csv

Reproduction
------------
Python 3 with NumPy and Matplotlib is required. From this directory, run:

    python finite_sinc_experiments.py --output-dir . --fft-power 17

The script regenerates every figure and data table. It also contains an exact
rational truncated-power evaluator, reciprocal-product coefficient generation,
and geometric Richardson weights.

To rebuild the report with a TeX Live installation:

    latexmk -pdf -interaction=nonstopmode -halt-on-error finite_sinc_products_report.tex

Research status
---------------
The report distinguishes results already present in the ProveIt documentation
from new theorems and conjectures developed here. The new material is proved in
the report but has not been independently peer reviewed or formalized in Lean.

> **Editorial note (2026-08-28):** the report source and compiled PDF listed above (and, where listed, the supplied source scan/OCR) were removed from this directory after their content was merged into the volume `Exponents_and_q_Series_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance list (and in `SHA256SUMS` here where present), and git history archives the files. This directory keeps only figures, data, and scripts.
