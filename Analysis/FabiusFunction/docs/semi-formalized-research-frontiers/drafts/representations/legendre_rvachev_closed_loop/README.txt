Legendre--Rvachev Biorthogonal Closure
======================================

Contents
--------

legendre_rvachev_closed_loop.tex
    Complete LaTeX source of the report.

legendre_rvachev_closed_loop.pdf
    Compiled report.

experiments.py
    Fully commented, self-contained symbolic and numerical experiment program.

Generated exact data
--------------------

legendre_coefficients_exact.csv
    Exact u_n through n=80, decimal values, and 2-adic valuations.

moments_and_reciprocal_coefficients.csv
    Exact even moments mu_{2m}, reciprocal-MGF coefficients gamma_{2m}, and
    observed valuations of mu_{2m}-1 through m=80.

spectral_sum_rules.csv
    Exact rational T_{m,l,r}^{(M)}, exact u_r, terms, and partial sums for four
    representative spectral closure identities.

finite_synthesis_checks.csv
    Independent inverse-FFT residuals for the finite shifted-up synthesis of
    P_l, l=0,...,5.

legendre_decay_high_precision.csv
    2300-digit Legendre coefficients and normalized log-square ratios through
    n=200.

Generated LaTeX and figures
---------------------------

low_degree_Q.tex
legendre_coefficients_table.tex
legendre_decay_ratios.png
spectral_sum_convergence.png
finite_synthesis_residuals.png
experiment_summary.txt

Source snapshot
---------------

The report audited the ProveIt repository at commit
73c85cb0023615311fdc4a5ff4951767bddeff34 (29 August 2026).

Requirements
------------

Python 3.11 or later
NumPy
Matplotlib
mpmath

Reproduce all data and figures
------------------------------

    python experiments.py

Omit figures:

    python experiments.py --no-plots

Useful options:

    --exact-n N            largest exact rational u_n (default and archived run: 80)
    --decay-n N            largest multiprecision u_n (archived run: 200)
    --dps N                mpmath decimal precision (archived run: 2300)
    --spectral-r N         largest r in spectral sum tables (archived run: 14)
    --synthesis-degree N   largest FFT synthesis check (archived run: 5)

Compile the report
------------------

    latexmk -pdf legendre_rvachev_closed_loop.tex

The program uses no network access.  Exact arithmetic is performed with
fractions.Fraction; floating-point calculations are used only for plots and the
independent Fourier-product check.
