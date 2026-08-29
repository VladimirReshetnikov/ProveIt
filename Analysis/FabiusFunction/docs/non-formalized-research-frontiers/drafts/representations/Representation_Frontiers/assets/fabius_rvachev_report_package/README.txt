FABIUS--RVACHEV REPRESENTATION REPORT PACKAGE
==============================================

Primary files
-------------
- fabius_rvachev_representations.pdf
  Rendered 30-page research report.

- fabius_rvachev_representations.tex
  Complete standalone LaTeX source.

- numerical_experiments.py
  Reproducible high-precision checks with detailed comments.

Numerical outputs
-----------------
- fourier_product_trace_checks.csv
- exterior_coefficients.csv
- dyadic_exterior_values.csv
- turan_inequalities.csv
- mellin_barnes_checks.csv
- trace_series_convergence.png
- turan_ratios.png
- mellin_barnes_errors.png

Research status
---------------
The report separates three categories:
1. formulas already present in the recursively audited ProveIt corpus;
2. deductions proved in the report, with novelty claimed only relative to the
   pinned repository corpus, not as an exhaustive claim of worldwide priority;
3. conjectures and future research directions, explicitly labeled as open.

Principal new operator package relative to the audited corpus
-------------------------------------------------------------
Let G be the inverse Dirichlet Laplacian on L^2(0,1) and
B = direct_sum_{n>=1} 4^{-n} G.  The report proves that the angular
Fourier transform of Rvachev's up-function is det(I-t^2 B), develops
its resolvent and heat representations, derives Brownian-bridge and
gamma-convolution laws, and obtains the exact exterior-power identity

  F(2^{-n}) = 2^{-n(n+1)/2}
              sum_{k<=n/2} Tr(wedge^k B)/(n-2k)!.

Reproducing the computations
----------------------------
Python dependencies:
- mpmath
- sympy
- matplotlib

From this directory run:

  python numerical_experiments.py

The script regenerates all CSV and PNG files in place.  On the build
system used for the delivered package, the direct products and
Mellin--Barnes integrals agreed at approximately 50 decimal digits.

Recompiling the report
----------------------
A recent TeX Live installation with pdfLaTeX/latexmk is sufficient.
Run:

  latexmk -pdf -interaction=nonstopmode -halt-on-error \
    fabius_rvachev_representations.tex

Audit anchor
------------
The recursive repository audit is anchored to commit
32d6d36c51d803289e6d6a0dc0c37753766eba47, as documented in the report.

Generated: 27 August 2026

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Representation_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.
