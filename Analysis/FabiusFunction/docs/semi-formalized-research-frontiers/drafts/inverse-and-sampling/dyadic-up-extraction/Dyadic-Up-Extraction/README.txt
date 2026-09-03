Exact Dyadic Extrapolation for Finite Rvachev Sinc-Product Splines
==================================================================

Files
-----

dyadic_up_extraction.tex
    Self-contained LaTeX source of the article.

dyadic_up_extraction.pdf
    Rendered article.

dyadic_up_extraction.py
    Standard-library Python program using exact fractions.  It evaluates the
    finite sinc-prefix splines, applies the q-Pochhammer extraction formula,
    reconstructs all geometric modes, computes reciprocal moment coefficients
    and dyadic derivatives, and verifies the recurrence with exact zero
    residuals.

verification_output.txt
    Output from the default exact verification suite.

Build
-----

    latexmk -pdf -interaction=nonstopmode -halt-on-error dyadic_up_extraction.tex

Run the exact verifier
----------------------

    python3 dyadic_up_extraction.py
    python3 dyadic_up_extraction.py --x 1/16 --check-through 10
    python3 dyadic_up_extraction.py --x=-3/32 --start 7 --check-through 12

The direct finite-spline evaluator is exponential in the prefix level because
it deliberately uses the transparent 2^(n+1)-term inclusion--exclusion formula.
It is intended for exact verification at moderate levels, not as a replacement
for faster bit-recursive evaluators in the ProveIt repository.
