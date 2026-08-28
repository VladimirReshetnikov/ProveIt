FABIUS INTEGRAL AND TRANSFORM FRONTIERS
=======================================

CONSOLIDATION NOTE
------------------
The standalone report source and PDF were absorbed into Part V of
../../Integration_and_Transform_Frontiers.tex. This directory now contains
only supporting assets; git history preserves the former standalone files.

Contents
--------

1. fabius_integrals_and_transforms_frontier_report.tex
   Complete LaTeX source for the research report.

2. fabius_integrals_and_transforms_frontier_report.pdf
   Rendered 29-page report.

3. numerical_experiments.py
   Self-contained, extensively commented numerical verification code.
   It implements finite Thue-Morse spline approximants, exact rational
   moments, quadrature, quantile inversion, and Newton-Mellin summation.

4. numerical_results.txt
   Human-readable output from the numerical experiments.

5. numerical_results.tex
   Compact generated tables included by the main LaTeX source.

Repository audit
----------------

The report was prepared after a recursive audit of the TeX corpus under:

  https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/FabiusFunction/docs

The audit distinguished canonical syntheses, current draft packages,
imported papers, generated TeX auxiliaries, and superseded archive copies.
Novelty statements in the report are deliberately repository-relative:
"new" means that an explicit formula or theorem was not located in that
audited corpus or in the targeted literature search; it is not an absolute
historical-priority claim.

Reproducing the numerical output
--------------------------------

From this directory, run:

  python numerical_experiments.py

Required Python packages:

  numpy
  scipy

The script rewrites numerical_results.txt and numerical_results.tex.

Compiling the report
--------------------

A current TeX Live installation with latexmk is recommended:

  latexmk -pdf -interaction=nonstopmode \
    fabius_integrals_and_transforms_frontier_report.tex

The source uses standard packages from TeX Live, including amsmath,
amsthm, mathtools, hyperref, cleveref, booktabs, longtable, multicols,
listings, and lmodern.

Numerical notes
---------------

The finite spline formulas use alternating Thue-Morse sums. Long-double
arithmetic and reflection symmetry are used through rank 10. At higher
ranks the cancellation becomes severe, so arbitrary precision is preferable.
The exact rational moment recurrence is independent of the spline model.
