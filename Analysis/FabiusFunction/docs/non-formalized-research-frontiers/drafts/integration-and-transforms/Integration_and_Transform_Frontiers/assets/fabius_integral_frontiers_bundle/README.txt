Integral and Transform Frontiers for the Fabius–Rvachev System
================================================================

ARCHIVED COMPANION BUNDLE
-------------------------

The former standalone manuscript is now consolidated in
../../Integration_and_Transform_Frontiers.tex, with the rendered report at
../../Integration_and_Transform_Frontiers.pdf. This directory retains its
supporting computations and figures.

CONTENTS
--------

../../Integration_and_Transform_Frontiers.tex
    Current consolidated LaTeX source of the research report.

../../Integration_and_Transform_Frontiers.pdf
    Compiled consolidated PDF.

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
preamble is required. From this directory, run three passes:

    (cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
    (cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
    (cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)

These commands update ../../Integration_and_Transform_Frontiers.pdf.

The supplied PDF was built with pdfTeX 1.40.26. The final build has 27 pages,
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
