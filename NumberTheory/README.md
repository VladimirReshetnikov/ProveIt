# Number Theory

- [`DiophantineEquations/`](DiophantineEquations/) contains FLT for exponent
  four, unconditional in both systems, under the same theorem names. Lean
  imports mathlib's theorem; the Coq development constructs the classical
  Fermat double descent from scratch (prime-divisor toolkit, coprime
  factors of squares, the primitive Pythagorean parametrization, and the
  odd-even descent core), with reduction theorems relating the three
  descent-step granularities.
- [`IntegerSums/`](IntegerSums/) proves the exact floor-square-root summation
  identity.
- [`RationalEnumeration/`](RationalEnumeration/) proves that the rational
  floor orbit enumerates every nonnegative rational exactly once.
- [`RiemannHypothesis/PAStatement/`](RiemannHypothesis/PAStatement/) defines a
  first-order PA sentence for the Mertens/Littlewood arithmetic criterion. It
  formalizes the statement, not yet its analytic equivalence with RH.
