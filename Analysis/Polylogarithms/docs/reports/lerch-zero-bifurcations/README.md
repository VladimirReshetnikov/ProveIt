# Lerch Endpoint Singularities and Stieltjes Zero Bifurcations

**All-order renormalization, nonmonotone branches, and a sharp fifth-index zero count**

A research continuation for Vladimir Reshetnikov's ProveIt project, prepared
October 9, 2026 (Pacific time). The reference repository commit is
`a2a4cf58c49c745058c40e4a6748d472a3420f18`.

Read `article/lerch_zero_bifurcations.pdf` for the complete article. Its editable,
self-contained LaTeX source is alongside the PDF.

## Principal results

The strongest exact root-count result is:

**The functions gamma_5'(a) and gamma_5''(a) each have exactly three positive
zeros. For every k >= 3, gamma_5^(k)(a) has exactly five positive zeros.
Every zero in these statements is simple.**

Here gamma_n(a) is the generalized Stieltjes constant, and the superscript
means differentiation in a, not in n. The theorem uses a proved global zero
bound, exact sign enclosures, and signs of predecessor functions on entire
critical-point brackets. Merely finding approximate roots would not prove the
deficit at the first two orders.

The analytic continuation results include an exact all-order decomposition of
the Lerch endpoint at rho=1. After normalization by exp(-a*mu), its entire nonanalytic part is mu^k times an
explicit polynomial of degree n+1 in log(mu), where mu=-log(rho). It yields
polylogarithmic order-derivative finite-part identities and the exact C^(k-1),
not C^k, endpoint smoothness threshold.

At (n,k)=(2,1), there are exactly two simple positive zeros for every
0 <= rho <= 1. The lower branch has a unique nondegenerate interior minimum;
the upper branch is strictly decreasing. Thus global decreasing monotonicity
of every branch is false at low derivative order. In contrast, for each fixed
n all branches strictly decrease once k is sufficiently large, with a uniform
explicit leading velocity. No effective optimal monotonicity threshold is
claimed.

At k=1, sufficiently small positive rho gives one simple positive zero for
odd n >= 3 and two for even n >= 2. The article proves a unique interior
left-hand fold for n=3. **The rho=0 endpoint retains a double zero at a=1**
and must be counted separately. Exclusion of an additional outer pair at
intermediate parameters below that fold is left as an explicit conjecture.

## Evidence and limitations

The article supplies ordinary mathematical proofs, supplemented where stated
by finite exact-arithmetic sign certificates. Neither the article nor the code
has been formalized in a proof assistant or externally refereed.

The starting Lerch expansion is classical (Erdelyi; DLMF 25.14.3_1), not a new
identity claimed by this report. New deductions are identified relative to
the inspected ProveIt manuscript; no exhaustive worldwide priority claim is
made. The mixed S4 special-value conjecture and numerical period independence
are not resolved here.

Numerical critical-point coordinates and sample root tables are diagnostics,
not isolating certificates. `certificates/sign_certificates.json` contains
the proof-bearing rational enclosures. The decimal endpoints printed in the
article's certified tables are outward coarsenings of those exact intervals.

## Package contents

- `article/`: complete TeX and compiled PDF, including proofs and eight research directions.
- `verification/certify.py`: standard-library-only outward integer interval verifier.
- `verification/test_exact.py`: 10,972 exact regression assertions, including 35 certificate replays.
- `verification/diagnostics.py`: independent Mellin-integral comparisons, endpoint residuals, and optional critical-point calculations.
- `verification/sample_branches.py`: reproduces the article's optional decimal root tables.
- `verification/symbolic_identities.py`: optional exact symbolic polynomial tables through degree ten.
- `certificates/`: executed exact, numerical, and symbolic output reports, clearly labelled.
- `integration/`: manuscript insertion, bibliography item, and proposed editorial corrections.
- `provenance/`: pinned source metadata, dependency/evidence ledger, and execution environment.

## Reproduce the proof-bearing computation

Use Python 3.10 or later. The delivered run used Python 3.13.5. No third-party
Python packages or network access are required for:

```sh
python verification/certify.py
python verification/test_exact.py
```

The verifier rejects optimized Python execution (`-O`), because assertion
checks must remain active. The two commands regenerate the sign and test
reports. Equivalently, use `make verify` on a system with make.

Parameters in the delivered certificates are 55 decimal fixed-point places,
72 rational logarithm-series terms, 32 initial Hurwitz summands, and 16
Euler--Maclaurin correction orders. No floating-point result decides a sign.
The mathematical error bound is proved in Section 10 of the article.

## Optional diagnostics and symbolic tables

```sh
python -m pip install -r requirements-optional.txt
python verification/diagnostics.py --full
python verification/sample_branches.py
python verification/symbolic_identities.py
```

The executed diagnostics compare 108 Mellin integrals with separate series or
Euler--Maclaurin evaluations, record 15 endpoint expansion residuals, and check
four direct polylogarithmic order derivatives. The symbolic script checks 42
formal identities. These optional checks are not substituted for the proof or
the exact sign certificates.

## Build the article

Use a LaTeX installation containing the standard AMS, Latin Modern, geometry,
booktabs, hyperref, bookmark, microtype, fancyhdr, and xurl packages:

```sh
make pdf
```

Without make:

```sh
cd article
pdflatex -interaction=nonstopmode -halt-on-error lerch_zero_bifurcations.tex
pdflatex -interaction=nonstopmode -halt-on-error lerch_zero_bifurcations.tex
```

The delivered PDF was rendered and visually checked. The short integration
fragment was smoke-compiled separately; the full repository manuscript was
not rebuilt. `integration/EDITORIAL_CHANGES.md` gives proposed placement and
exact old/new text for two corrections in the existing half-unit proof.

No remote repository file was changed, and no commit or pull request was
created. The package is prepared for review and integration, not already
integrated.
