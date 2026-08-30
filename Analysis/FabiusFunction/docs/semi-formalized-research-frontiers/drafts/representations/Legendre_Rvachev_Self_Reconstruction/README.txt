LEGENDRE--RVACHEV SELF-RECONSTRUCTION PACKAGE
=============================================

Generated: 29 August 2026
Repository snapshot: faa3a9b94ac0e71abdc53c36fdf428222e4d2a8c
Repository scope audited: Analysis/FabiusFunction/docs/**/*.tex

MAIN FILES
----------

legendre_rvachev_self_reconstruction.tex
    Complete LaTeX source of the report.

legendre_rvachev_self_reconstruction.pdf
    Compiled 27-page report.

legendre_rvachev_experiments.py
    Standalone, extensively commented Python program.  It computes the exact
    rational moment, reciprocal-MGF, Legendre, deconvolution, and spectral data;
    verifies the finite shifted-up synthesis, quarter-grid null relation, and
    lifting law; and regenerates all tables and figures.

CORPUS_AUDIT.md
    Snapshot, source map, imported/new boundary, and targeted novelty searches.

REPOSITORY_SNAPSHOT.txt
    Exact Git revision used for the final corpus-relative audit.

data/
    CSV certificates and numerical summaries.

generated/
    Vector-PDF and PNG versions of all figures used in the report.

SHA256SUMS.txt
    Checksums for every distributed file except SHA256SUMS.txt itself.

REPRODUCING THE COMPUTATIONS
----------------------------

Requirements:

  * Python 3.11 or newer;
  * NumPy;
  * Matplotlib.

From this directory, run:

    python legendre_rvachev_experiments.py

This regenerates data/*.csv, data/verification_summary.txt, and all figures.
Useful alternatives are:

    python legendre_rvachev_experiments.py --no-plots
    python legendre_rvachev_experiments.py --max-spectral-mode 120
    python legendre_rvachev_experiments.py --help

All theorem-level verification tests use Python's Fraction type and return the
exact rational residual 0.  Floating point is used only for the million-atom
coefficient scan and plotting.

RECOMPILING THE REPORT
----------------------

Run from this directory so that the relative generated/ figure paths resolve:

    latexmk -pdf -interaction=nonstopmode -halt-on-error \
        legendre_rvachev_self_reconstruction.tex

A standard TeX Live installation with the packages named in the source
preamble is sufficient.  The delivered PDF was compiled with pdfTeX and then
rendered page-by-page for visual inspection.

KEY VERIFIED OUTPUT
-------------------

  * Exact finite shifted-up synthesis for Legendre degrees 0 through 6;
  * exact P_4 quarter-grid null relation, m=16 -> 64;
  * exact N=1 -> 2 coefficient and function lifting identities;
  * positive rational energy partial sum through N=100:

        0.40443676798398526

The last decimal is a stabilized numerical display of an exact positive
rational partial sum, not an independently certified enclosure of the limit.
