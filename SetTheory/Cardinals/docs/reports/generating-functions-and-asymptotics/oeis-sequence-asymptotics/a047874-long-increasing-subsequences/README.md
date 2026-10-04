# Finite Fredholm Truncation for Long Increasing Subsequences

A proof of fixed-sector holonomicity and uniform all-orders tail asymptotics.
Prepared for Vladimir Reshetnikov, October 3, 2026.

## Main results

Let A(N,k) count permutations of N letters with LIS exactly k and T(N,k)
count those with LIS at least k. For a Young diagram lambda, let
Y_k(lambda) = #{i >= 1 : lambda_i - i >= k-1}, and let
C_j(N,k) = sum_{lambda |- N} (f^lambda)^2 binom(Y_k(lambda),j).

The article proves:

* Every fixed-j array C_j is holonomic, by an explicit 4j-variable
  proper-hypergeometric sum derived from discrete Bessel correlations.
* T_R = sum_{j=1}^R (-1)^(j+1) C_j agrees exactly with T when
  N < (R+1)(k+R). Taking the k-difference gives an extension of A.
  Choosing R=r-1 proves holonomicity in every fixed sector N<=rk.
* The first discrepancy at equality is exactly a signed squared rectangle
  tableau dimension. The cutoff is sharp for this construction.
* T/B has a uniform all-orders expansion exp(-2 rho) sum c_d(rho)/k^d,
  where rho=(N-k)/k and B=(N!)^2/(k!^2(N-k)!). An explicit recurrence
  computes the coefficient polynomials. The omitted shifted-row
  contribution is zero or bounded by exp(-c N log N) relatively to B.
* A269021 has the expansion
  16^n (n-1)!/(pi e^2) times
  [1 + 3/(4n) + 137/(32n^2) + 757/(128n^3)
   - 41429/(2048n^4) - 3803959/(40960n^5) + O(n^-6)].

The article also gives exact single sums, rational-ray P-recursiveness,
exact-length asymptotics (including A267433), and conditional statistics.

## Status

This is an unrefereed conventional proof, not a Lean/Rocq formalization.
It establishes the fixed-sector **existence conjecture** in Kauers--Wang
(arXiv:2609.02220v1, September 2026). It does not certify their specific
one-third-sector guessed operators or claim minimal recurrence orders.

The fourth-order A269021 recurrence was already proved by Kauers--Wang.
The leading asymptotic is already recorded in OEIS, and the A267433
leading equivalent has a 2023 proof by David Moews. These are credited.
The discrete Bessel kernel, Robinson--Schensted correspondence, and
holonomic summation are established external inputs, not new claims.
Priority beyond the checked sources remains unverified.

## Contents

- `article.pdf`: complete article, including proofs and further questions.
- `article.tex`: standalone LaTeX source, with inline bibliography.
- `verify.py`: independent exact enumeration, rational Bessel-series
  checks, symbolic coefficient generation, and numerical diagnostics.
- `results/`: CSV/JSON outputs and coefficient formulas.
- `SOURCE_AUDIT.md`: source identities, novelty boundaries, and audit scope.
- `requirements.txt`, `build.sh`: reproduction aids.

## Reproduce

Python 3.10 or newer is required (the union type annotations use Python 3.10 syntax).
The core exact checks use only the standard library:

```sh
python verify.py --core-only --output results
```

For the complete run:

```sh
python -m pip install -r requirements.txt
python verify.py --output results
```

A complete run checks 378 (N,k) cells for N<=26, truncation ranks 1..4,
140 independent Bessel-minor values, and 16 published initial terms of
each of A269021 and A267433. It generates 61 terms of each diagonal.
Symbolic tests derive five orders, verify 15 finite-product specializations,
and independently derive the exact-length corrections. Numerical diagnostics
use 100 decimal digits. They are not interval-certified bounds.

Build the PDF using a TeX distribution containing amsmath, amsthm,
mathtools, newtx, microtype, booktabs, enumitem, fancyhdr, listings,
xcolor, and hyperref:

```sh
sh build.sh
```

The source does not require BibTeX, external figures, downloaded files,
or network access. Tests supplement the written proof; finite agreement
is never used as a substitute for the all-parameter theorems.
