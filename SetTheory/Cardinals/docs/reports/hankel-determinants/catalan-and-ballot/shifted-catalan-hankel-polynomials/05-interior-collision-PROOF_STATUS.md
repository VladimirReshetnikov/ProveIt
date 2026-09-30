# Proof status

## Universal statements proved in the article

1. **Theorem 3.1:** exact convergent one-cluster sector expansion, all fixed degrees,
   all nonendpoint complex bases, every coordinate collision, derivative-uniform
   compact convergence, and absolute weighted remainder order.
2. **Theorem 5.1:** explicit complete first Taylor coefficient, with multiplication
   by the coordinate sum and an Euler differential operator.
3. **Theorem 6.1:** explicit analytic radius and Cauchy remainder bound, including
   collisions. The constants are conservative, not optimized.
4. **Theorem 7.1:** exact convergent extension to multiple separated nonendpoint
   clusters, with explicit nonzero cross-cluster constants.
5. **Theorem 10.1:** leading symmetric-pair limit and its explicit phase-dependent
   first correction for every fixed multiplicity.
6. **Theorem 12.1:** first displacement, uniqueness, reality, and simplicity of a
   finite-size root near any fixed simple real limiting root.
7. **Theorem 12.2:** genuinely convergent zero expansion whose coefficient at
   inverse-size order ell is a Laurent polynomial of degree at most ell in the
   fast phase.
8. **Corollary 13.2:** for the degree-two example, a full interval of scaled zero
   limits at an irrational base angle, finitely many phase limits at rational
   angles, and exact cancellation at the central base angle.

The numbering above matches the supplied article; the underlying proof flow is
also documented in Appendix A.

## Classical ingredients and rederivations

The Catalan moment measure and orthogonal polynomials, the Christoffel polynomial
modification identity, its bilinear kernel variant, and divided-difference
confluence are established mathematics. Self-contained proofs are given for the
normalizations used here. The centered exponential Vandermonde is an elementary
repackaging of the ordinary Vandermonde identity.

The limiting oscillatory Jacobi moment determinant belongs to the established
kissing-polynomial literature. Its even-parity nondegeneracy, odd oscillatory
zeros, and large-frequency analysis are not claimed as newly discovered. The
article independently derives the needed statements and constants, including
Gram positivity and finite polynomial integration-by-parts asymptotics.

## Computational audit

All 518 assertions passed in the recorded run:
- 392 exact Fraction-arithmetic assertions.
- 126 high-precision numerical assertions, at 100 decimal digits.

Additional CSV experiments document finite-size corrections, root transport,
multiple clusters, and profile asymptotics. These experiments are not additional
universal certificates. Numerical root decimals are not certified isolating
intervals. The code uses Gaussian elimination, recurrence jets, and high-precision
coefficient extraction; no proof-assistant checker or outward-rounded interval
arithmetic was used.

## Not claimed

- Peer review, Lean/Rocq formalization, or interval certification.
- Worldwide priority for every identity, coefficient, or application.
- New discovery of classical sine-kernel or kissing-polynomial results.
- Uniformity as a base approaches an endpoint or a different base.
- Growing-degree uniformity, unbounded scaled coordinates varying with N, or
  root indices growing with N.
- A classification of all nonsimple zeros or all recurrence resonances.
- Constant-coefficient recurrences for a moving multiplier q_N.
- Validation of every theorem or file in the source repository.

The precise resolved target is the fixed-degree nonendpoint moving-root question
explicitly proposed in the inspected repository/predecessor reports.
