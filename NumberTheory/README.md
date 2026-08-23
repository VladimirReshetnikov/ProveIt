# Number Theory

- [`DiophantineEquations/`](DiophantineEquations/) contains FLT for exponent
  four, unconditional in both systems, under the same theorem names. Lean
  imports mathlib's theorem; the Coq development constructs the classical
  Fermat double descent from scratch (prime-divisor toolkit, coprime
  factors of squares, the primitive Pythagorean parametrization, and the
  odd-even descent core), with reduction theorems relating the three
  descent-step granularities.
- [`IntegerPoints/`](IntegerPoints/) formalizes the results of Zhai–Cao (1999)
  and Wu (2002) on the primitive circle problem under RH, together with their
  exponential-sum machinery.  Lean proves Zhai–Cao Lemmas 1–6, 8 and 9,
  Graham–Kolesnik Lemmas 3.1–3.5 (including both curvature signs of stationary
  phase), and several further reductions and auxiliary estimates; the
  remaining deep exponential-sum estimates and RH-conditional main theorems
  are still unproved.  The formal statements are derived from the OCR
  transcriptions in `IntegerPoints/Papers/`.
- [`IntegerSums/`](IntegerSums/) proves the exact floor-square-root summation
  identity.
- [`RationalEnumeration/`](RationalEnumeration/) proves that the rational
  floor orbit enumerates every nonnegative rational exactly once.
- [`RiemannHypothesis/PAStatement/`](RiemannHypothesis/PAStatement/) defines a
  first-order PA sentence for the Mertens/Littlewood arithmetic criterion. It
  formalizes the statement, not yet its analytic equivalence with RH.
