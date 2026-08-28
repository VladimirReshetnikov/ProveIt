Inverse Frontiers for the Fabius--Rvachev System
=================================================

This archived companion directory preserves the figures, data, and
reproducibility scripts from the former standalone report.  The report itself
is now incorporated into the consolidated source and PDF two levels above
this directory.

Contents
--------
- ../../Inverse_and_Sampling_Frontiers.tex : consolidated LaTeX source
- ../../Inverse_and_Sampling_Frontiers.pdf : consolidated rendered report
- figures/                           : the three figures included by the source
- data/                              : numerical tables, constants, and exact symbolic-check log
- generate_data.py                   : regenerates the numerical tables and figures
- verify_symbolic_fast.py            : exact rational verification for r <= 12 through Q^12

Compile
-------
Run from this directory:

    cd ../..
    pdflatex -interaction=nonstopmode -halt-on-error Inverse_and_Sampling_Frontiers.tex
    pdflatex -interaction=nonstopmode -halt-on-error Inverse_and_Sampling_Frontiers.tex
    pdflatex -interaction=nonstopmode -halt-on-error Inverse_and_Sampling_Frontiers.tex

The PDF uses only standard TeX Live packages and the bundled figures.
The Python scripts are not needed to compile the report.  To rerun them, install
Python 3 with sympy, mpmath, and matplotlib.

The geometric Lagrange-moment obligation is discharged post-snapshot at Lean
checkpoint 1e761ed77583e9870ceeaeb2c74ac824094f0f3f.  The inverse-germ,
uniform-remainder, quarter-sign/enclosure, and endpoint-reversion obligations
retain their explicit frontier status in the report.

Scope and priority note
-----------------------
The report's novelty claims are relative to the recursively inspected 57-file
repository corpus.  It does not claim unconditional global publication priority.
