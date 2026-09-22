# Exact Linearization Domains and Resonant Boundary Cycles in Surcomplex Dynamics

A 24-page research manuscript with a standalone LaTeX source, a compiled PDF,
and exact finite symbolic checks. Prepared 21 September 2026 for the Surreal
project.

## Main result

Let K = C((t^Gamma)), with Gamma a nonzero divisible ordered abelian group of
arbitrary rank. For a nonlinear polynomial f(z) = lambda*z + O(z^2), assume
v(lambda) = 0 and lambda is not a root of unity. If its residue has order q,
write f^q(z) = lambda^q*z + sum b_n*z^n and delta = v(lambda^q - 1).
The article proves that the exact maximal centered valuation ball of
normalized Hahn linearization is

    { z : v(z) > r },   r = max_{b_n != 0} (delta - v(b_n))/(n - 1).

The bounding valuation sphere contains points of exact period q. A finite
ordinary polynomial gives their count with multiplicity, residue directions,
and leading return multipliers. The proofs include an arbitrary-rank support
certificate, a common-domain holomorphic lifting theorem in the resonant
case, a perturbation certificate, and workspace invariance up to No[i].

An explicit cubic cancellation family changes the exact threshold from
delta/2 to delta/4 and changes the number of closest two-cycles. A classical
non-Brjuno example shows why infinitesimal Hahn summability does not imply
common-domain analyticity in the nonresonant case.

“Bounding sphere” is an algebraic valuation-shell expression, not the
actual topological boundary of a ball. All infinite evaluations use strong
Hahn summation, not limits of surreal partial sums.

## Contents

- `article.pdf`: the 24-page manuscript, with proofs and bibliography.
- `article.tex`: standalone LaTeX source; no external bibliography or graphics.
- `verify.py`: 54 exact finite symbolic checks.
- `verification.txt`: the recorded successful run.
- `requirements.txt`: the SymPy version used for the recorded run.
- `Makefile`: optional build and verification targets.
- `validation.txt`: compilation and PDF validation summary.

## Build the article

From this directory, using a standard TeX Live or MiKTeX installation:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

The bibliography is embedded in the source. No BibTeX step, network access,
or external figure files are required. The optional `make pdf` target runs
the same command. On Windows the direct `latexmk` command works in PowerShell.

## Reproduce the finite checks

Use Python 3.10 or newer with SymPy:

    python -m pip install -r requirements.txt
    python verify.py

The recorded run used Python 3.13.5 and SymPy 1.14.0 and passed all 54 checks.
The test script uses exact arithmetic, not floating-point experiments. It
checks return coefficients, cancellations, initial polynomials, multiplier
ratios, finite Schröder recurrences, and initial coefficients of the coherent
linearizer. It is not an arbitrary Hahn-field implementation, a proof
assistant, or a verification of the transfinite arguments.

## Research status and provenance

The exact resonant finite-return formula, its arbitrary-rank support control,
the common-domain lifting, and the explicit cancellation analysis are offered
as proposed original results. The article distinguishes these from established
Hahn support theory, algebraic closure, formal linearization, and Lindahl's
rank-one nonresonant result. No named published conjecture is claimed solved.
Priority has not been certified; this is an AI-assisted, unrefereed manuscript,
not a formally verified proof development.

The repository comparison used the catalogues at commit
`39f2be6667ade51bca2b45daa47e289d69c09764` of
`VladimirReshetnikov/Surreal`, specifically `docs/README.md`,
`docs/surcomplex/analysis/README.md`, and
`docs/surcomplex/analytic-geometry/README.md`, together with a targeted search
for linearization. It was not a line-by-line audit of every research package.
Primary literature consulted is cited in the article, including Lindahl,
Neumann, Poonen, Yoccoz, and Bournez–Guilmant.
