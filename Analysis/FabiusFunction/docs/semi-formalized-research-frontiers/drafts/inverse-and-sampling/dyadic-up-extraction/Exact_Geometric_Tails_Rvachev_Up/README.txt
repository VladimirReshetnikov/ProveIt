EXACT GEOMETRIC TAILS FOR FINITE-SINC APPROXIMANTS
==================================================

This archive contains the article and exact-arithmetic companion program for
recovering Rvachev's up-function at a dyadic rational x from finitely many
finite-product spline values up_n(x).

Files
-----

up_dyadic_extraction.tex
    Complete LaTeX source.

up_dyadic_extraction.pdf
    Rendered 21-page article.

up_dyadic_extraction.py
    Standard-library Python 3.9+ implementation.  It evaluates finite splines
    by the exact Thue-Morse truncated-power formula, constructs q-Pochhammer
    extraction weights, computes Bell-Bernoulli coefficients and dyadic
    derivatives, and verifies the main identities using fractions.Fraction.

verification.txt
    Output of the bundled exhaustive exact-arithmetic check through dyadic
    level 7.

SHA256SUMS.txt
    SHA-256 checksums for the four files above.

Principal formula
-----------------

Let m be the least nonnegative integer such that 2^m x is integral, put

d = floor(m/2),    rho = 1/4,    q_n = up_n(x).

For every N >= m,

              1       d
up(x) = ------------- sum (-1)^k rho^(k(k+1)/2) [d choose k]_rho q_(N+d-k).
         (rho;rho)_d  k=0

The article proves the stronger exact law

up_n(x) = up(x) + sum_{j=1}^d C_j(x) 4^(-j n),

with no remainder once n >= m.  At odd dyadic levels m >= 3, the law already
holds at n=m-1.  All coefficients C_j and the corresponding even derivatives
of up are recoverable from the same d+1 values.

Run the code
------------

    python up_dyadic_extraction.py --examples
    python up_dyadic_extraction.py --x 1/16
    python up_dyadic_extraction.py --verify-level 7

The verification command supplied in verification.txt checked 2376 exact
rational identities at all 255 interior dyadic points through exact level 7.
No floating-point tolerance was used.

Build the PDF
-------------

A TeX Live installation with the packages used in the preamble is sufficient.
The source prefers Libertinus and falls back to Latin Modern.

    latexmk -pdf -interaction=nonstopmode -halt-on-error up_dyadic_extraction.tex

The supplied PDF was built with pdfTeX and visually checked after rendering all
pages to PNG.
