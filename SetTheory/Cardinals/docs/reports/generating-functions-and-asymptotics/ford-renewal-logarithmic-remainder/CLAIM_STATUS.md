# Claim status

## Proved in the manuscript

| Claim | Nature of proof | Scope |
| --- | --- | --- |
| Exact positive remainder measure | Bounded positive self-adjoint operator and Stieltjes inversion | All n >= 1; both spectral endpoints and singular measure are addressed. |
| Strict complete monotonicity and Hankel positivity | Positive integrals | Every finite order and every positive starting index. |
| Explicit finite bounds | Elementary density inequalities | Constants 1/200 and 10 for n >= 4096; a separate pi-squared bound for all n >= 2. |
| Sharp remainder and all inverse-log orders | Real Laplace integrals and a finite geometric identity | Fixed truncation order; exact leading constant 1. |
| All algebraic orders | Convergent polylogarithm identity and uniform Taylor remainder | Logarithmic coefficient integrals remain intact; truncation order is fixed. |
| Product constant and tail enclosures | Positive moment identity and exact finite geometric remainder | Exact inequalities in terms of rho, gamma, and finitely many recurrence terms. |
| Inverse accuracy law | Logarithmic inversion and a positive derivative lower bound | Real accuracy threshold; integer index is the ceiling of the exact real root. |
| Difference and tail expansions | Positive moment summation and controlled sum-integral comparison | Fixed finite-difference order. |
| Kernel universality theorem | Same spectral argument under explicit assumptions | Local C1, endpoint C2, positive kernel, and nonnegative Schur-complement condition. |

The main infinite statements have not been externally refereed or
kernel-checked in Lean. Independent derivations during preparation agreed
on the spectral representation, endpoint constant, coefficient signs,
algebraic sectors, and product/inverse normalizations. The final audit added
an explicit total-variation estimate for the weighted sum-integral error.

## Established prior material

The recurrence, its pole amplitude, and its application to totient-volume
estimates are from prior work. Ford's revised paper already gives a bounded
absolute error, its negative sign and monotonicity, and the unweighted exact
sum. Spectral measures, Hausdorff moments, gamma identities, and the
polylogarithm expansion are classical tools. They are credited in the article.

## Novelty boundary

The package proves a sharp refinement of the estimate in the inspected Ford
paper. It does not assert a resolution of a named famous conjecture or
established worldwide priority. The full Ford-Lau Monthly solution was
unavailable to inspect. The exact density, all-orders expansion, product
correction, and universality theorem should be compared against that source
and its later citations before any priority claim is made.

## Numerical artifacts

The recurrence, quadrature, eigenvalue calculations, constants, and plots use
floating arithmetic. They are reproducibility and consistency diagnostics.
They do not use outward rounding and are not interval certificates. The
symbolic checker proves its finite symbolic identities, not the analytic
theorems that use them. The observed finite product is not a certified
decimal enclosure of the infinite product.

## Claims not made

- No new arithmetic error bound for the full distinct-totient count.
- No validation of the larger claims in the openai/math manuscript.
- No assertion that a fixed logarithmic truncation improves at every index
  when one more term is included.
- No uniform theorem with a growing truncation order or difference order.
- No exact integer rounding from a truncated inverse expansion near an integer.
- No repository mutation, pull request, or publication.
