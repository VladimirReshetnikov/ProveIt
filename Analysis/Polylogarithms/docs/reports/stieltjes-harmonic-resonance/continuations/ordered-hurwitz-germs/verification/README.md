# Verification and evidential scope

Run from the package root:

```sh
python verification/verify.py --part all
```

The completed run passed **278 exact assertions**, rejected **one deliberate
corruption**, and passed **33 floating-point comparisons** at 55 working
decimal digits. The numerical comparisons are diagnostics, not rigorous
interval certificates. They are not substituted for the analytic proofs.

## Exact suite

The 278 assertions comprise one six-permutation ray identity, 36
monomial divided-difference coefficients, three nonlinear reparametrization
coefficients, one tangential-path constant, seven reciprocal-Gamma
coefficients computed independently by integer partitions and a Newton
recurrence, one explicit cubic normalization, 144 finite stuffle tests,
and 85 exact cyclotomic residue indicators. A changed six-permutation
formula is rejected in a separate corruption control.

The finite stuffle checks replace logarithms by arbitrary rational labels;
this tests the exact finite index and merge algebra. It does not certify
asymptotic limits of logarithmic sums. Those are proved in the article.

## Integral and Gamma suite

Thirty comparisons cover the elementary master at positive, negative,
and complex orders; the full-half-plane Hurwitz master at six parameter
pairs (including a+z=0); the all-depth elementary hierarchy through depth
six; orientation coefficients by quadrature versus a digamma-tail
expansion, including a=0.7; Gamma-ratio coefficients by complex Cauchy
extraction versus Newton recurrence; and polygamma primitive derivatives.
The largest recorded absolute discrepancy is 2.852928e-38.

Near t=0, the implementation uses Bernoulli subtraction for the kernel
and an incomplete-beta endpoint series for the shifted generating
function. This avoids treating exp(-t)=1 after rounding as the original
function's true argument. Reciprocal Gamma handles a+z=0.

## Independent ordered-ray suite

Two nonsymmetric depth-three finite parts are extracted from a separate
Euler--Maclaurin nested-zeta evaluator. That evaluator does not use the
holomorphic-germ theorem as its evaluation formula. The slopes are
(1,1,2) and (1,2,1); a=1; the circle radius is 0.025; there are 32 Cauchy
nodes; the tail cutoff is N=36; and the Euler--Maclaurin truncation has
10 terms. A third comparison changes the cutoff to N=48 and 12 terms
at an ordinary non-diagonal point. The largest discrepancy is
1.178359e-32.

An initial 24-node diagnostic had approximately 1e-24 positive-mode
aliasing and did not meet its 1e-25 threshold. The completed default run
uses 32 nodes. This is a numerical-resolution correction, not an
adjustment of the mathematical identity or a proof of a remainder bound.

## Records and environment

`results_exact.json`, `results_integrals.json`, and `results_rays.json`
retain actual values, discrepancies, thresholds, parameters, run times,
and software versions. `orientation.json` gives diagnostic coordinates;
`summary.json` gives machine-readable aggregate status.

Tested environment: Python 3.13.5, mpmath
1.3.0, SymPy 1.14.0.
The code runs locally and makes no network requests. Executing it
replaces the corresponding results JSON files; it does not alter any
remote repository. `check_manifest.py` verifies the packaged byte hashes.
