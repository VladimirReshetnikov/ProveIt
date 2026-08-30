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
From a clean directory, run exactly three serial passes:

for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
    fabius_iterates_nowhere_analytic.tex
done

Validated repository build (2026-08-30)
---------------------------------------
- 19 A4 pages using the canonical 27 mm geometry and Libertinus prose.
- All PDF fonts are embedded and subset Type 1 fonts; no Type 3 fonts occur.
- The final log has no warnings, unresolved references, or overfull/underfull boxes.
- All pages have extractable text and render successfully; the title/status box,
  theorem boundary, numerical figures, conjecture section, and source map were
  inspected visually.
- The source map names the live Monotonicity.lean module.
- The numerical script and Lean sources were not rerun during document-policy
  normalization; the supplied PNG figures and their numerical_output copies remain
  byte-identical.
