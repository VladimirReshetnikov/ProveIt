UNIT-CIRCLE, BESSEL, AND SPECTRAL REPRESENTATIONS PACKAGE
=========================================================

Main files
----------
rvachev-fabius-representations.tex   LaTeX source of the report
rvachev-fabius-representations.pdf   Rendered report
numerical_experiments.py             Exact/high-precision reproducibility code
numerical_results.txt                Human-readable verification log
corpus_audit.txt                     Source and nonduplication ledger

Generated data and figures
--------------------------
chebyshev_moments.csv
jacobi_coefficients.csv
schur_parameters.csv
generated_tables.tex
bessel_convergence.{png,pdf}
mgf_bessel_convergence.{png,pdf}
verblunsky_coefficients.{png,pdf}

Reproducing the calculations
----------------------------
Run from this directory:

    python numerical_experiments.py

The script uses exact fractions for moments, Jacobi coefficients, and Schur
parameters; mpmath for high-precision analytic checks; and matplotlib for the
figures. Dependencies are listed in requirements.txt.

Recompiling the report
----------------------

    python /home/oai/skills/pdfs/scripts/latex_to_pdf.py \
        rvachev-fabius-representations.tex \
        -o rvachev-fabius-representations.pdf

Run numerical_experiments.py first because the report inputs
`generated_tables.tex` and includes the generated figures.
