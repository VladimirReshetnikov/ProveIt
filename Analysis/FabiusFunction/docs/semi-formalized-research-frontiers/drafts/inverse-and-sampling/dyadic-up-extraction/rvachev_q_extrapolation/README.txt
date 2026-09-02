Exact geometric tails and q-binomial extrapolation for dyadic Rvachev values
============================================================================

Files
-----
rvachev_q_extrapolation.tex
    Complete LaTeX source of the article.

rvachev_q_extrapolation.pdf
    Rendered article.

exact_extrapolation.py
    Fully rational, standard-library Python implementation and verification.

verification_output.txt
    Output of the included exact verification run through dyadic depth 6.

Reproducing the numerical checks
--------------------------------
Run from this directory:

    python exact_extrapolation.py --max-depth 6 \
        --output verification_output.txt

Every identity is checked with fractions.Fraction. No floating-point
arithmetic is used in the exact tests.

Building the PDF
----------------
A standard TeX Live installation is sufficient:

    pdflatex rvachev_q_extrapolation.tex
    pdflatex rvachev_q_extrapolation.tex
    pdflatex rvachev_q_extrapolation.tex

The additional passes resolve the table of contents, theorem aliases, and
cross-references.  Equivalently, use ``latexmk -pdf`` when available.
