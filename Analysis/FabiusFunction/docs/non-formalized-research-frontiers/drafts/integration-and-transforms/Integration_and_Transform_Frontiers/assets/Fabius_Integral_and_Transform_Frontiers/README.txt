FABIUS INTEGRAL AND TRANSFORM FRONTIERS
=======================================

ARCHIVED COMPANION BUNDLE
-------------------------

The former standalone manuscript is now consolidated in
../../Integration_and_Transform_Frontiers.tex, with the rendered report at
../../Integration_and_Transform_Frontiers.pdf. This directory retains its
supporting computations.

Contents
--------

1. ../../Integration_and_Transform_Frontiers.tex
   Current consolidated LaTeX source for the research report.

2. ../../Integration_and_Transform_Frontiers.pdf
   Rendered consolidated report.

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

A current TeX Live installation is sufficient. From this archived companion
directory, compile the consolidated source three times:

  (cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
  (cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
  (cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)

These commands update ../../Integration_and_Transform_Frontiers.pdf.

The source uses standard packages from TeX Live, including amsmath,
amsthm, mathtools, hyperref, cleveref, booktabs, longtable, multicols,
listings, and lmodern.

Numerical notes
---------------

The finite spline formulas use alternating Thue-Morse sums. Long-double
arithmetic and reflection symmetry are used through rank 10. At higher
ranks the cancellation becomes severe, so arbitrary precision is preferable.
The exact rational moment recurrence is independent of the spline model.
