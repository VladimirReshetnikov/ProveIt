Inverse Frontiers for the Fabius--Rvachev System
=================================================

Contents
--------
- Fabius_Inverse_Frontier_Report.tex : complete LaTeX source
- Fabius_Inverse_Frontier_Report.pdf : compiled 29-page report
- figures/                           : the three figures included by the source
- data/                              : numerical tables, constants, and exact symbolic-check log
- generate_data.py                   : regenerates the numerical tables and figures
- verify_symbolic_fast.py            : exact rational verification for r <= 12 through Q^12

Compile
-------
Run from this directory:

    latexmk -pdf -interaction=nonstopmode Fabius_Inverse_Frontier_Report.tex

The PDF uses only standard TeX Live packages and the bundled figures.
The Python scripts are not needed to compile the report.  To rerun them, install
Python 3 with sympy, mpmath, and matplotlib.

Scope and priority note
-----------------------
The report's novelty claims are relative to the recursively inspected 57-file
repository corpus.  It does not claim unconditional global publication priority.
