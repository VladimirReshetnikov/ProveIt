# The Exponential Scale of Gregory Sign Thresholds

Research package, 19 September 2026.

## Main result

Define G_n^(m) by (x/log(1+x))^m = sum G_n^(m) x^n, and let Gr(m)
be the **least** N such that (-1)^(n-1) G_n^(m) > 0 for every integer n >= N.
The manuscript proves

    log Gr(m) = m + 1 - EulerGamma
                - (zeta(2)+zeta(3))/m + C2/m^2 + O(m^-3),

    C2 = zeta(2)*zeta(3) + zeta(2) - zeta(3)
         - (5/2)*zeta(4) - 3*zeta(5).

It also gives a finite algorithm for every coefficient of the complete
asymptotic expansion. In particular,

    Gr(m) / exp(m) -> exp(1-EulerGamma) = 1.52620511159586388047...
    Gr(m+1) / Gr(m) -> e
    Gr(m) / 3^m -> 0.

The target is Conjecture 6.1 of Xu and Zhao, arXiv:2609.11072v1. The
printed lower bound already conflicts with its reported value Gr(5)=113;
this package independently certifies that value. The large-order theorem
is the substantive replacement for the proposed growth law and does not
rely on that small-index inconsistency.

## Start here

Read `gregory_sign_threshold.pdf`. Its editable source is
`gregory_sign_threshold.tex`.

From this directory, with Python 3.10 or newer:

```sh
python code/verify_exact.py
```

This uses only the standard library. It recomputes every saved rational
certificate, checks all signs, independently compares polynomial-integral
totals with a generating-function recurrence, and compares the result to
`data/exact_certificates.json`. Do not invoke Python with `-O`.

The certificate proves Gr(3)=11, Gr(4)=36, Gr(5)=113, and Gr(6)=346.
The elementary cases Gr(1)=1 and Gr(2)=4 are established in the article;
the program also checks the finite arithmetic used for them.

To regenerate the certificate rather than compare it:

```sh
python code/verify_exact.py --write
```

## Optional symbolic and numerical reproductions

The versions actually used were Python 3.13.5, SymPy 1.14.0, and mpmath
1.3.0. The optional dependencies are listed in `requirements.txt`.

```sh
python -m pip install -r requirements.txt
python code/derive_asymptotics.py --output data/asymptotic_coefficients.txt
python code/numerical_roots.py
```

The symbolic program generates P1 through P4 and corrections C1 through
C3 by default. `--corrections 2` gives a smaller computation; higher values
are supported but become more expensive.

The numerical program compares 64-node and 96-node Gauss-Legendre rules
on every unit interval. It saves continuous-zero estimates for selected
orders through 50, precision settings, and quadrature discrepancies.
These numerical roots and their ceilings are **not exact certificates**.
Agreement of two quadrature orders is not a rigorous error enclosure.

## Build the article

A standard TeX installation with the packages in the preamble is needed
(in particular newtx, amsmath/amsthm/mathtools, tcolorbox, and hyperref).
No font files are distributed in this archive.

```sh
pdflatex -halt-on-error gregory_sign_threshold.tex
pdflatex -halt-on-error gregory_sign_threshold.tex
```

Alternatively, `sh build.sh` runs exact verification and builds the PDF.
`sh build.sh --full` also reruns the symbolic and numerical programs.

## Why a local root is enough here

The central logical step is the cumulative-positivity lemma in Section 3.
If the signed coefficient kernel at one integer index N has nonnegative
cumulative integral on its support and a positive total, the kernel at
every later integer n is obtained by multiplying by a positive decreasing
function. Integration by parts preserves positivity. In the large-order
proof, a polynomial-sized positive margin on [0,2] beats an exponentially
small absolute tail on [2,m]. This certifies **all** subsequent n, not just
a long observed run of signs.

The analytic reduction uses a compactly supported extension of
-1/Gamma(-t). An untruncated gamma expectation of this function would not
be integrable. Section 5 explicitly addresses that issue.

## Status and limits

This is an AI-generated research draft, not an externally refereed paper.
The asymptotic theorem is supported by the written proof; the scripts do
not constitute a proof-assistant formalization of that analysis. Exact
arithmetic certificates depend on the correctness of Python and of the
mathematical propagation lemma. Symbolic computations check the finite
coefficient algebra. Numerical quadrature is exploratory only.

No claim is made to classify every continuous zero at every finite order,
to prove convergence of the full formal expansion, or to give explicit
constants and a numerical starting order for the asymptotic error bounds.
No claim of exhaustive literature priority is made, and no external
submission or contact with the conjecture's authors was performed.

`SOURCE_AUDIT.md` records the precise source and the scope of the status
check. Original third-party papers and font files are not included.
