NOWHERE ANALYTICITY OF FABIUS COMPOSITIONAL ITERATES
====================================================

Main files
----------
- fabius_iterates_nowhere_analytic.tex : complete LaTeX source
- fabius_iterates_nowhere_analytic.pdf : rendered report
- numerical_experiments.py            : commented reproducible diagnostics

Numerical output
----------------
The numerical_output/ directory contains the CSV, metadata, and four generated
plots.  The script synchronizes those four plots into figures/; the LaTeX report
embeds fabius_iterates.png, spine_comparison.png, and spine_remainder.png, while
taylor_root_diagnostic.png remains a synchronized supplementary diagnostic.

Reproduce the numerical diagnostics
-----------------------------------
MPLBACKEND=Agg python numerical_experiments.py \
  --output-dir numerical_output --figure-dir figures \
  --x0 0.437123456789 --iterate-count 4 --max-order 22

Dependencies: Python 3, NumPy, SciPy, Matplotlib.
The CSV writer fixes LF line endings on every platform.  Exact PNG bytes and
the last floating-point digits require the pinned Linux/Python environment in
REPOSITORY_AUDIT.md; other environments should be checked numerically, not by
requiring identical hashes.  No numerical result is a premise of the proof,
and the floating-point replay is not independent symbolic verification.

Formalization status
--------------------
The 1,555-line source and its current 21-page A4 PDF now crosswalk the exhaustive three-definition,
thirty-three-theorem `PartitionDefect.lean` API.  That Lean module proves the
finite positive-list defect decomposition, zero and sharp-equality
classifiers, fixed-block lower bound, and first positive shell.  It does not
construct set partitions, prove the weighted Bell sum or its asymptotics, or
prove nowhere analyticity for any positive compositional iterate; those
manuscript steps remain paper-only.

Compile the report
------------------
Run exactly three serial passes from this directory:

pdflatex -interaction=nonstopmode -halt-on-error fabius_iterates_nowhere_analytic.tex
pdflatex -interaction=nonstopmode -halt-on-error fabius_iterates_nowhere_analytic.tex
pdflatex -interaction=nonstopmode -halt-on-error fabius_iterates_nowhere_analytic.tex

The source uses the repository's canonical A4, 27 mm, Libertinus preamble.
After a successful build, inspect every rendered page and remove the generated
.aux, .log, .out, and .toc sidecars before committing the matching PDF.
