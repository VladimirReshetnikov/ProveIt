Exact q-Extrapolation of Finite Sinc-Product Splines at Dyadic Points
=====================================================================

Prepared for Vladimir Reshetnikov
Date: 2 September 2026

CONTENTS
--------

dyadic_up_extraction.pdf
    The rendered 26-page article.

dyadic_up_extraction.tex
    Complete LaTeX source.

verify_dyadic_up_extraction.py
    Exact-arithmetic verification and experiment program.  It evaluates the
    finite splines from their Thue-Morse truncated-power formula, constructs
    the q-Pochhammer extraction weights, solves the rational geometric
    Vandermonde system, checks the eventual law and annihilating recurrence,
    and optionally regenerates the figures.

verification_report.txt
    Summary of the exhaustive exact verification through dyadic depth 7.

sample_sequences.csv
    Representative exact rational sequences Q_n(x).

geometric_coefficients.csv
    Recovered exact geometric-mode coefficients for representative points.

finite_splines.pdf / finite_splines.png
    Figure showing finite sinc-product splines.

geometric_mode_cancellation.pdf / geometric_mode_cancellation.png
    Figure illustrating exact cancellation of the geometric correction modes.

SHA256SUMS
    SHA-256 checksums for all files in this directory except SHA256SUMS itself.

MAIN RESULT
-----------

For a dyadic x in [-1,1], define

    s = min{r >= 0 : 2^r x is an integer},
    d = floor(s/2),
    rho = 1/4,

and let Q_n(x) be the inverse Fourier transform of

    product_{k=0}^n sinc(pi t / 2^k)

at x.  The article proves the exact eventual identity

    Q_n(x) = up(x) + sum_{m=1}^d C_m(x) rho^(m n),    n >= s,

where

    C_m(x) = (-1)^m a_m 4^(-m) up^(2m)(x)

and the rational a_m are the coefficients of the reciprocal infinite sinc
product.  Thus no limiting process is needed once n reaches s.

From any d+1 consecutive samples beginning at n_0 >= s,

    up(x) = sum_{j=0}^d W_{d,j} Q_{n_0+j}(x),

with the q-Pochhammer weights

    W_{d,j} = (-1)^(d-j) rho^((d-j)(d-j+1)/2)
              / ((rho;rho)_j (rho;rho)_{d-j}).

The article also gives the equivalent q-binomial and integer-coefficient base-4
forms, formulas for every C_m, an annihilating recurrence, stability estimates,
and worked examples.

REPRODUCING THE EXACT CHECKS
----------------------------

Python 3.10 or later is recommended.  The exact checks use only the Python
standard library.  Matplotlib is needed only to regenerate the figures.

From this directory, run:

    python verify_dyadic_up_extraction.py --out-dir . --max-depth 7 --skip-plots

To regenerate the figures as well, omit --skip-plots:

    python verify_dyadic_up_extraction.py --out-dir . --max-depth 7

The verified run included 257 dyadic points, 2,570 sequence/window identities,
941 analytic-versus-fitted coefficient identities, and 1,542 recurrence checks,
all performed with fractions.Fraction exact arithmetic.

COMPILING THE ARTICLE
---------------------

A standard TeX Live installation with pdflatex and the packages named in the
preamble is sufficient.  From this directory, run:

    latexmk -pdf -interaction=nonstopmode -halt-on-error dyadic_up_extraction.tex

The two PDF figure files must remain beside the TeX source.
