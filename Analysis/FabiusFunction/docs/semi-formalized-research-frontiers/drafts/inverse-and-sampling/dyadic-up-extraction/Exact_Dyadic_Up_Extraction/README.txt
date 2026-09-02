Exact q-Binomial Extraction of Rvachev Up-Function Values
=========================================================

Contents
--------

dyadic_up_extraction.tex
    Complete LaTeX source of the 20-page article.

dyadic_up_extraction.pdf
    Rendered article.

verify_dyadic_extraction.py
    Fully commented exact-arithmetic implementation.  It evaluates finite
    sinc-product splines through the Thue-Morse truncated-power formula,
    constructs q-Pochhammer/Gaussian-binomial extraction weights, solves the
    q-Vandermonde system for all geometric coefficients, and verifies the
    annihilating recurrence.

experiment_output.txt
    Captured output from the verification script.  The exhaustive regression
    covers every reduced dyadic point through denominator 2^6 and reports zero
    exact rational residuals.

Main formula
------------

For a dyadic x of depth d, M=floor(d/2), Q=1/4, and n>=d,

  up(x) = 1/(Q;Q)_M * sum_{j=0}^M (-1)^(M-j)
          * Q^binom(M-j+1,2) * [M choose j]_Q * up_{n+j}(x).

Here up_n is the inverse Fourier transform of the product over k=0,...,n.

Reproduce
---------

Run the exact experiments with:

  python3 verify_dyadic_extraction.py

Compile the article in a standard TeX Live installation with:

  latexmk -pdf dyadic_up_extraction.tex

The source uses only common LaTeX packages and has no external assets.
