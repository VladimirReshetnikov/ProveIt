INTERPOLATION ON A GEOMETRIC COMB
=================================

This archive accompanies the report

  Interpolation on a Geometric Comb:
  Lagrange Filters, Jackson--Newton Series, q-Analogues,
  and the Fabius--Rvachev Bridge

prepared from the 30 August 2026 snapshot of Vladimir Reshetnikov's
ProveIt repository, with the q-Pochhammer/q-binomial monograph and the
adjacent Fabius/Rvachev reports used as the main corpus references.

CONTENTS
--------

  geometric_comb_interpolation.tex
      Complete LaTeX source of the report.

  geometric_comb_interpolation.pdf
      Rendered 36-page A4 report.

  geometric_comb_experiments.py
      Reproducible exact-arithmetic and high-precision experiments.
      The script contains detailed comments and assertions checking the
      main finite identities used in the numerical section.

  NUMERICAL_SUMMARY.txt
      Compact summary of selected exact and high-precision outputs.

  data/*.csv
      Exact Fabius moments and dyadic values, geometric interpolants,
      Lagrange-row norms, and reciprocal Rvachev-filter data.

  figures/*.{pdf,png}
      Vector and raster versions of the five report figures.

  requirements.txt
      Python package requirements for regenerating the experiments.

  SHA256SUMS.txt
      SHA-256 hashes of the packaged source, report, code, data, and figures.

PRINCIPAL DEVELOPMENTS IN THE REPORT
------------------------------------

The report develops, among other things:

  * the geometric Vandermonde/Gaussian-Pascal factorization;
  * closed barycentric and arbitrary-target Lagrange cardinal formulas;
  * the exact L1 norm of the zero-extrapolation row;
  * the complete Mellin symbol of the dilation filter and its responses to
    fractional powers and logarithmic corrections;
  * the identity between geometric divided differences and iterated Jackson
    derivatives, including a locally convergent infinite Newton series;
  * a regular-summability theorem at the accumulation point;
  * a proved exact convergence-set theorem for nonzero superflat data;
  * a geometric-uniform extension of the Fabius comb/moment identity for
    0 < q <= 1/2;
  * exact Gaussian and Mersenne transforms of the Fabius moments;
  * a reciprocal sinc-product filter for the Rvachev up-function;
  * explicit bridges to shifted up-function synthesis and the finite
    Thue--Morse spline hierarchy;
  * explicitly labeled conjectures and research problems.

REPRODUCING THE NUMERICAL OUTPUT
--------------------------------

From this directory, with Python 3.9 or later:

  python -m pip install -r requirements.txt
  python geometric_comb_experiments.py --output-dir . --max-order 80

The half-base q=1/2 calculations through order 80 use Python Fraction and are
exact.  Floating-point arithmetic is used only for infinite sinc products,
error plots, and decimal presentation; those calculations use mpmath at 100
decimal digits.

COMPILING THE REPORT
--------------------

A standard TeX Live installation with latexmk is sufficient.  Run:

  latexmk -pdf -interaction=nonstopmode -halt-on-error \
      geometric_comb_interpolation.tex

The source uses common packages including amsmath, amsthm, mathtools,
graphicx, booktabs, tabularx, listings, hyperref, and cleveref.  Libertinus is
used when installed, with Latin Modern as the fallback.

VALIDATION PERFORMED
--------------------

The packaged PDF was compiled without LaTeX warnings or overfull/underfull
box reports, rendered to all 36 page images at 200 dpi for visual inspection,
and passed the supplied PDF preflight checks (openable, unencrypted, and not
scan-only).  All fonts reported by pdffonts are embedded.
