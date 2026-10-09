# Proof and evidence map

The labels below match the article source and are stable even if its section
numbering changes. A code check is not an independent proof of the analytic
lemmas it depends on.

| Result | Main dependencies | Computational role |
|---|---|---|
| `thm:laplace`: common kernel | Classical Hurwitz Mellin integral, parameter derivative identity, dominated coefficient extraction | 12 numerical master/integral comparisons |
| `thm:hyperbolic`: simple real roots of P_n | Reciprocal-gamma product; elementary real-root-preserving differential operator; coefficient limits | Polynomial coefficients and derivatives checked symbolically; no finite root scan is used to prove all n |
| `thm:zerobound`: at most n zeros, multiplicities included | Exponential-polynomial Chebyshev bound proved by Rolle; signed Laplace-transform lemma | Analytic proof, no numerical zero-count inference |
| `thm:propagate`: persistent saturation and right-interlacing | Rolle, decay at infinity, global zero bound | Analytic proof |
| `cor:lowindices`: exact n zeros for n=1,...,4, all k | 14 rational sign certificates at k=1; global bound; propagation | Computer-assisted finite base case, standard-library exact verifier |
| `thm:ray`: eventual n zeros and full expansions | Gamma concentration, uniform differentiated Taylor expansion, simple kernel zeros, global bound | 80 symbolic regression checks include moments, inverse-root algebra, and polynomial/cumulant formulas |
| `thm:first`: unique first-index zero and half-unit bracket | Strict covariance sign and increasing/decreasing gamma tilts | Entirely analytic proof; no finite base-case dependency |
| `cor:firstasymp`: explicit three-term first-index location | General root expansion and direct derivative ratios | Symbolic correction check; nine numerical root computations |
| `thm:jet`: normalized L-jet transport | Primitive Dirichlet functional equation, simple trivial zeros, factorial-normalized germ | 24 numerical jet checks through fourth order, both parities, including a nonreal character |
| `thm:characterkernel`: two universal parity kernels | Character decomposition, jet transport, exact gamma/rising-factorial cancellation | Six generating-function and six second-index character-coordinate checks |
| `thm:EM`: exact finite derivative enclosure | Euler–Maclaurin with periodic Bernoulli remainder; positive logarithm-moment bound | Exact implementation accepts 30 signs; 16 of them give eight width-10^(-20) first-index root brackets |
| `cor:effective`: terminating threshold certificate search | Eventual saturation, computable rational enclosures, dovetailing | Existence argument only; no production threshold-search implementation or efficiency claim |

## Boundaries

- The derivative-tower master identity is existing mathematics and explicitly credited.
- The all-k zero count for n=2,3,4 is computer-assisted, not purely analytic.
- Exact saturation for arbitrary n at k=1 is not claimed.
- No global error constant is inferred from numerical asymptotic residuals.
- No special-value arithmetic independence is claimed.
- The original formal rank formula is not disproved; its printed proof is incomplete.
- No Lean files with placeholders, axioms, or uncompiled claims are included.
- The 80 exact symbolic identities are regression tests, not a proof-assistant verification.
- The 48 high-precision tests are finite numerical consistency checks, not certificates.
- Novelty in the literature has not been established, and external peer review remains necessary.

## Suggested formalization order

Begin with the polynomial operator and the elementary exponential-polynomial
zero bound. Next formalize the exact rational/logarithm enclosure arithmetic
and Euler–Maclaurin bound. Then add Mellin coefficient extraction, the Laplace
variation argument, and propagation. Gamma concentration and the functional
 equation can be developed independently after that reusable core.
