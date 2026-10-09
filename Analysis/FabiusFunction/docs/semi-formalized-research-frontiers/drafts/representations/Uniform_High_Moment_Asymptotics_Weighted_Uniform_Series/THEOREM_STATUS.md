# Theorem and verification status

## Proof ledger

| Article label | Statement | Evidence supplied | Limits |
|---|---|---|---|
| `lem:single`, `lem:array` | Uniform tilted moment, cumulant, and analytic-disk bounds | Direct integral, coefficientwise, and Cauchy proofs | Constants not optimized |
| `prop:root` | Unique, well-conditioned saddle in `(n,2n)` | Real-variable proof | Numerical solver is not interval-certified |
| `prop:fourier` | Exact gamma-kernel Fourier identity and array-independent tails | Fourier transform, inversion, and Fubini proof | No CLT for the tilted sum is asserted |
| `thm:main` | All fixed orders with `O_J(mu*/n^(J+2))` remainder | Uniform local expansion, tail estimates, and one-extra-order argument | J fixed; constants and thresholds not numerically optimized |
| `thm:geosharp` | Sharp fixed-q logarithmic rates; first-corrected `O_q(n^-3)` | Cumulant-defect bounds and exact coefficient identities | q fixed for these improved bounds |
| `thm:transfer` | Universal original-tilt polynomial transfer | Global pointwise Taylor bound and moment polynomials | Perturbative only when the remainder is small |
| `thm:crossover` | Explicit `15/sqrt(n)` bound and iff criterion | Pointwise kernel estimate and variance-controlled smoothing proof | Constant 15 is not claimed optimal |
| `thm:criticalcorrection`, `cor:criticalgeometric` | Critical correction and optimal uniform error order | Taylor/cumulant proof and explicit varying-q family | Actual tilted mean must be retained |
| `prop:periodic` | Periodic Laplace-product representation | Exact product splitting and tail estimate | Periodic factor must not be replaced by a constant |
| `prop:fabiusidentity` | Exact Fabius dyadic/moment relation | Classical identity reproduced with normalization and proof | Not claimed new |
| `cor:fabius` | Improved relative dyadic asymptotics | Exact transfer of the moment estimates | Same unrefereed status as the main analytic proof |

## What was checked computationally

`data/validation.json` records **119 checks, zero failures**, at 70 decimal
digits for numerical checks. Exact symbolic tests include the first correction
in two forms, deterministic cancellations, gamma calibrations through C3,
the C2 gradient, and the Laplace coefficient recursion. Rational tests cover
geometric moments and an independent equal-weight Stirling formula. Numerical
tests cover product derivatives, mesh brackets, saddle roots, and finite
comparisons. The tables use 80 digits and independently computed reference
moments, not the asymptotic formulas as their own reference.

## What is not claimed

- No newly kernel-checked Lean or Rocq theorem.
- No independent referee or priority determination.
- No computer proof of all asymptotic quantifiers.
- No outward-rounded interval certification of the numerical outputs.
- No uniformity in a growing correction order, convergent expansion, or optimal truncation result.
- No uniform fixed-q computational complexity when q itself varies.
- No use of any major conjectural/announced OpenAI Math result as an assumption.

The analytic statements are presented with proofs, rather than as conjectures;
independent review remains appropriate before publication or formal integration.
