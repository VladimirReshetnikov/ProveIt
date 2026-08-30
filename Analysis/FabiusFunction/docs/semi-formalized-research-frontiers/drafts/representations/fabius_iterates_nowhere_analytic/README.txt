NOWHERE ANALYTICITY OF FABIUS COMPOSITIONAL ITERATES
====================================================

Main files
----------
- fabius_iterates_nowhere_analytic.tex : complete LaTeX source
- fabius_iterates_nowhere_analytic.pdf : rendered report
- numerical_experiments.py            : commented reproducible diagnostics

Numerical output
----------------
The numerical_output/ directory contains the CSV, metadata, and generated plots.
The figures/ directory contains copies used by the LaTeX report.

Reproduce the numerical diagnostics
-----------------------------------
python numerical_experiments.py --output-dir numerical_output \
  --x0 0.437123456789 --iterate-count 4 --max-order 22

Dependencies: Python 3, NumPy, SciPy, Matplotlib.
No numerical result is used as a premise of the proof.

Compile the report
------------------
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  fabius_iterates_nowhere_analytic.tex
