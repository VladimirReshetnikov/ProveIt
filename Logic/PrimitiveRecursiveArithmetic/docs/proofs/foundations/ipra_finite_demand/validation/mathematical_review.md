# Mathematical and formal-status review

The report received focused cross-review of the foundation/aggregate,
root-support, and norm-certificate arguments before delivery. This is
a record of the checks and corrections, not an independent machine
verification of the main theorems.

## Proof-critical checks

- Backward demands use a fixed endpoint and a quantifier-free guarded
  invariant. The demand need not be monotone. Uniformity is over a
  fixed finite PR language or explicit certificates, not a universal
  unclocked PR program evaluator.
- The nearest-neighbor tail bound is geometric. The sampled membership
  target uses the stronger 5/8 error margin needed to obtain the stated
  rational inequality. Selection is explicitly allowed to depend on
  the enumeration and seed.
- Approximate minimization uses the corrected constant 4L+2. The
  complex-modulus example uses Lipschitz constant 2 for the sup metric.
- Rational deflation remains finite. Intermediate coefficient bounds
  are separated from the final product root bound. Adequacy is stated
  using rational samples with explicit slack, not undecidable comparisons
  of exact complex roots. The descent lemma remains a named inherited
  human-proof dependency.
- The norm proof accounts for several points in a single fiber. It uses
  evaluation rows and divisibility of distinct determinant rows, then
  synthetic division at distinct abscissae. The Vandermonde determinant
  argument is made explicit. No smoothness of the curve is assumed.
- Coprimality yields a unique maximal weighted coefficient index.
  The corresponding cyclic determinant term has a nonzero leading
  coefficient; no cancellation from another term is possible.
- The subspace conclusion bounds distinct points in finite lists. It
  supplies no coordinate-height cutoff, approximation cover, or quotient
  representative producer.

## Formalization boundary

The five modules compile. Only the scheduling and finite-cover core
contain the advertised proved native lemmas. The other modules contain
concrete executable definitions and named unproved propositions. There
are no custom axiom declarations or admitted proofs asserting those
propositions. The norm targets currently specialize to rational
coefficients and rational points; the written coded-field generality
is a further definition-generalization step. Native Lean correctness
is kept distinct from an embedded `Prf PRAAx` derivation.

The native rational triangle proof has `Classical.choice` in its printed
axiom dependency through Std rational-order results. This is disclosed;
the report's object-level plan uses explicit integer rational arithmetic.
See `lean_build.json` for the exact source hashes, compiler output, and
printed axiom audits. Exact Python checks are separate finite evidence.
