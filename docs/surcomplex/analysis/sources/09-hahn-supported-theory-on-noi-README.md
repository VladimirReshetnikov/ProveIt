# Surcomplex Analysis

A Hahn-Supported Theory of Holomorphic Functions on No(i)

## Contents

- `surcomplex_analysis.pdf`: the article, including proofs, examples, a hypothesis audit, and references.
- `surcomplex_analysis.tex`: standalone LaTeX source with embedded bibliography.
- `verify_examples.py`: exact finite symbolic checks of the worked examples.
- `verification.txt`: output of a successful verification run.
- `Makefile`: build and check commands.

## Build

A standard TeX Live or MiKTeX installation with the packages named in the
source is sufficient. Run:

    latexmk -pdf surcomplex_analysis.tex

Alternatively run `pdflatex surcomplex_analysis.tex` twice (a third pass may
be required after the table of contents changes pagination).

## Check the examples

Python 3.10 or later and SymPy are required:

    python verify_examples.py

The checker uses exact arithmetic for truncated formal power series. It is
not a surreal-number implementation and does not mechanically verify the
general support and factorization proofs.

## Principal results

The article constructs faithful infinitesimal Taylor evaluation for
Hahn-supported holomorphic coefficient functions, proves a constructive
Weierstrass preparation theorem, and shows that an order-m zero of the
leading complex coefficient produces exactly m surcomplex zeros in its
entire monad, counted with multiplicity. This gives a Cauchy formula,
a residue theorem for actual surcomplex poles, an argument principle,
and a leading-order Rouche theorem. It also includes local inverse and
ramification theorems, open mapping and maximum modulus, a residue-level
Liouville theorem, and a coefficientwise Montel theorem.

## Scope

Hahn summation is not convergence of ordinary partial sums. The contour
integral is defined coefficientwise on ordinary contours (and specified
affine rescalings), not as a Riemann integral in the all-surreal-radii
topology. A connected ordinary complex domain and its monadic thickening
have different topologies. The hypotheses and limits of the framework
are made explicit throughout the article.

Known surreal analytic foundations and the existing Ehrlich--Kaplan
surcomplex exponential are attributed to their sources. The article does
not claim that surcomplex analysis was previously undeveloped, that every
classical theorem transfers, or that this research-style treatment has
been independently refereed.
