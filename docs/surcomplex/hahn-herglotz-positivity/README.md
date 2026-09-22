# Positivity without a Positive Measure
## Hahn–Herglotz normalization and strict moment hierarchies in surcomplex analysis

Research manuscript, 22 September 2026. Prepared for Vladimir Reshetnikov.

## Contents

- `article.pdf`: the 26-page manuscript (cover, contents, and 24 numbered pages).
- `article.tex`: complete editable LaTeX source, including the bibliography.
- `verify.py`: exact symbolic identities and exhaustive finite checks.
- `verification.txt`: captured output from the verification script.
- `requirements.txt`: tested SymPy dependency.
- `build.sh`: three-pass PDF build command.
- `research_audit.md`: repository comparison, source audit, and novelty limitations.

## Main results

The manuscript proves an arbitrary-rank constant-congruence normalization theorem for coherent matrix Hahn–Herglotz functions; a Harnack comparison requiring strict slack; an exact transfinite null-ideal criterion for positive coefficientwise Hahn measures; and a positive-functional representation obstruction, even for pointwise completely positive unital Hahn-linear functionals.

The principal explicit example has c_0 = 1 and c_n = -epsilon for n != 0. Every ordinary finite Toeplitz matrix is strictly positive, but the unique signed coefficientwise boundary measure is (1+epsilon)m - epsilon delta_1 and is negative on {1}. Positive quadratures, fixed-leading Haar/Fejer approximations, exact Schur iterates, a cyclic algebraic unitary realization, and a strict five-level hierarchy are developed around this example. A finite-prefix extension theorem shows that arbitrarily prescribed finite infinitesimal moment data can extend to each of five different boundary-regularity behaviors.

The coefficientwise category is essential: ordinary finite signed regular Borel measures form the coefficients; the boundary is the ordinary circle; countable additivity is coefficientwise. The counterexamples do not rule out other non-Archimedean measure theories or enlarged boundary spaces.

## Build

A TeX Live installation with the packages named in the preamble of `article.tex` is sufficient. In a POSIX shell:

```sh
./build.sh
```

Alternatively, run `pdflatex -halt-on-error article.tex` three times. No BibTeX run is needed. The build writes auxiliary files and per-pass logs locally; those are not included in the distributed archive.

## Run the finite checks

Python 3.10 or later is required; this delivery was checked with Python 3.13.5 and SymPy 1.14.0.

```sh
python -m pip install -r requirements.txt
python verify.py
```

The script uses a formal epsilon, never a floating-point surrogate. It checks exact rational identities, finite Toeplitz determinant/eigenvector formulas, Schur recursion with symbolic n, root-of-unity quadrature moments, Fejer formulas, distribution Fourier signs, and 19,683 finite three-level/three-atom measure arrays. All implemented checks passed.

These tests are not formal verification of the infinite and transfinite theorems. In particular they do not prove Hahn summability, measure uniqueness, the analytic minimum principle, or the transfinite null-ideal argument. Those are justified in the mathematical proofs in the article.

## Research status

This is a candidate-original theorem package, not a claimed solution of a named published open conjecture. Classical ingredients are explicitly separated from the Hahn-level conclusions. The repository audit is pinned to commit `4cf691c7d951e037739d32d9f5c387dcce724f3c` and is targeted rather than exhaustive. In particular, the ZIP interiors were not fully inspected and the code-search endpoint reported incomplete results. Priority and absence from every repository file cannot be certified from this audit. No independent referee review or Lean verification is claimed.
