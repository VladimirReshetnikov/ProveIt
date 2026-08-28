Dyadic Self-Sampling, Alias Superconvergence, and Rvachev-Appell Deconvolution
================================================================================

Contents
--------
Fabius_Dyadic_Self_Sampling_Frontier_Report.tex
    Complete LaTeX source.
Fabius_Dyadic_Self_Sampling_Frontier_Report.pdf
    Compiled report.
experiments.py
    Reproducible exact and high-precision computations.
quadrature_table.csv / quadrature_table.tex / quadrature_table_display.tex
    Exact rational phase-adapted quadrature data and compact PDF display.
spectral_check.tex / spectral_check_display.tex
    Independent comparison between exact rational defects and the spectral series.
harmonic_tail_table.tex
    First-harmonic dominance ratios.
appell_polynomials.tex
    Exact inverse-moment Rvachev-Appell polynomials through degree 10.
appell_root_counts.csv
    Exploratory nonreal-root counts through degree 30.
appell_root_certificate.txt
    Exact Sturm count for A_8.
defect_profiles.png, quadrature_weights.png, appell_roots.png
    Figures used by the report.

Reproducing the computations
----------------------------
Required Python packages: mpmath, sympy, matplotlib.

Exact checks and tables only:
    python experiments.py --no-plots

Exact checks, tables, and figures:
    python experiments.py

Compiling the report
--------------------
Run from this directory so the generated tables and figures are found:
    latexmk -pdf -interaction=nonstopmode -halt-on-error \
      Fabius_Dyadic_Self_Sampling_Frontier_Report.tex

Research-status convention
--------------------------
The report distinguishes proved results, exact computer-assisted results, and conjectures.
"New" means new relative to the audited ProveIt repository snapshot, not a claim of
worldwide priority.
