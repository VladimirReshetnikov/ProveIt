Integral and Transform Frontiers for the Fabius–Rvachev System
================================================================

CONTENTS
--------

fabius_integral_frontiers.tex
    Complete 29-page LaTeX source of the research report.

fabius_integral_frontiers.pdf
    Compiled A4 PDF.

numerical_experiments.py
    Fully commented, deterministic numerical checks and figure generation.

numerical_results.txt
    Console output from the final numerical run.

functions_and_primitives.png
pushforward_cdf.png
fractional_defect.png
    Figures included by the LaTeX report.

requirements.txt
    Python package versions used for the final numerical run.

SHA256SUMS.txt
    SHA-256 checksums for every packaged file except itself.

REPRODUCING THE NUMERICAL EXPERIMENTS
-------------------------------------

Tested with Python 3.13.5. From this directory, run:

    python numerical_experiments.py

This rewrites numerical_results.txt and the three PNG figures. The script uses
only deterministic quadrature, FFT convolution, interpolation, and arbitrary-
precision product/summation calculations; it does not access the network.

RECOMPILING THE REPORT
----------------------

A TeX distribution containing pdfLaTeX and the standard packages named in the
preamble is required. From this directory, run exactly three passes, then
remove the sidecar files:

    pdflatex -interaction=nonstopmode -halt-on-error fabius_integral_frontiers.tex
    pdflatex -interaction=nonstopmode -halt-on-error fabius_integral_frontiers.tex
    pdflatex -interaction=nonstopmode -halt-on-error fabius_integral_frontiers.tex
    rm -f *.aux *.log *.out *.toc

The supplied PDF was built with pdfTeX 1.40.26. The final build has 29 pages,
resolved cross-references, and no reported LaTeX warnings or overfull boxes.

SCOPE AND PROOF STATUS
----------------------

The report was audited against the current canonical Fabius-function volumes,
the current frontier syntheses, the inverse-function draft, and the repository's
recursive path/archive ledgers. Historic files that are explicit ancestors or
near-duplicates are treated as one lineage rather than as independent sources.
"New" means not found in that audited repository corpus; no claim of worldwide
priority is made without an external literature proof.

Statements labeled theorem, proposition, or corollary are supplied with proofs
in the report. Statements labeled conjecture or research direction are not
claimed as proved. Numerical experiments are corroborative checks rather than
substitutes for proofs.

CURRENT LEAN STATUS
-------------------

The reusable normalized Volterra layer was focused-build verified at compiled
checkpoint e109088ed. Its affine covariance is division-free for every real
scale, while the inverse form assumes a nonzero scale. Its basepoint formula
works without endpoint ordering and includes order zero; the positive-order
zero-tail theorem needs no endpoint-value hypothesis. Separately, the signed
global and bounded x <= 1 natural-monomial Fabius coefficients are formalized
by normalizedVolterra_pow_mul_extendedFabius and
normalizedVolterra_pow_mul_fabiusReal_of_le_one. The report's 1-F, shifted-up,
and exterior piecewise coefficient specializations remain paper-level results.
