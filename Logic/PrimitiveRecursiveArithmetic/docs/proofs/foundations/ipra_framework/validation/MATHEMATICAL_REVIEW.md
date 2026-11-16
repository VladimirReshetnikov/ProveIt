# Mathematical review notes

These are review checks performed during preparation, not an external
peer-review certificate and not a replacement for the proofs in the article.

## Foundations

- Bounded universal Booleanization fixes the final bound and its universal
  premise before applying quantifier-free induction to a guarded prefix.
  The reverse direction fixes the tested index before induction.
- Bounded existential Booleanization uses a stored witness and equations
  for a failing-prefix fold. It does not circularly assume the existential
  Booleanization theorem in its own search invariant.
- The bounded-loop context is independent of the induction variable.
  Unbounded assumptions remain premises; only the invariant is Booleanized.
- The fixed-program, finite-table, and clocked-trace interfaces are kept
  distinct. A PR universal evaluator is not postulated.
- The inspected native equivalence is used only to transport a supplied
  arithmetic derivation. Semantic Lean proofs are not reported as object
  iPRA proofs.

## Represented analysis

- Rational slack removal uses an explicit common denominator and one
  precision determined by its binary length.
- The finite gate invariant includes the original operand bound, the
  perturbed operand bound, and local rounding. The chosen error budget
  preserves the side condition that previous errors are at most one.
- The integral construction compares two finite grids. A finite rational
  separation argument justifies the exact non-strict output bound.
- The represented monotone-window proof never floors a represented value.
  It minimizes rational endpoint differences and keeps the explicit
  positive margin `2^(-k)/(2K)`.
- The infinite regularity and monotonicity premises are not called bounded
  merely because their index range is bounded. Their precision quantifiers
  remain explicit premises, used at particular instances.
- The coherent selection schedule is `tau(k) = max(k,sigma(k))`; both
  monotonicity and the supplied quantitative isolation modulus are used.

## Implicit branch and producer

- All coefficient and iteration inductions are first established for
  finite rational arrays with fixed degree and horizon.
- Clipping coefficients to their majorants preserves the exact contraction
  certificate. Clipping whole sampled arrays preserves the weighted ball.
  Both projections increase a known approximation error by at most two.
- The coefficient-name construction uses iteration `s+r*k+3` and finite
  evaluation error at most `2^(-s-3)`.
- The finite weighted coefficient bound uses a common iteration horizon,
  not an induction asserting an infinite series property.
- The pointwise fixed-point identity is proved by a finite residual
  estimate, so infinite substitution is not an unstated assumption.
- The simple-root certificate producer has explicit `U,h,T,p,W,t`.
  The Gaussian sampling convention is norm-one error `2^(-t)` for every
  coefficient, root, and inverse name; componentwise names use one extra
  precision bit.
- The producer proves its rational inverse sample is nonzero, and
  contraction uniqueness proves that the branch passes through the
  supplied root. A positive derivative gap supplies the inverse name.
- The Gaussian prototype and 72 exact checks cover negative and nonreal
  centers, nonreal inverse values, and signed coefficient effects. These
  checks supplement the general written proof.

## Diophantine argument

- The integer power gap covers all signs and both exponent parities; the
  full integer statement is also a compiled semantic Lean theorem.
- The leading-term lower bound and the loss estimate are applied only
  when their factors are nonnegative. The nonzero-remainder root bound
  is established separately before applying the integer power gap.
- Polynomial completion matches the entire top coefficient interval.
  Its nonzero known divisor and positive common denominator are explicit.
- The exact-polynomial-power branch is separated from the finite-point
  branch, including the possible sign of an even-power leading root.
- The family proof excludes `x = -2,1,2` uniformly after obtaining
  `|x| <= 2`, then checks `x = -1,0` by parity.
- Bounded-denominator transport uses the three specified homogenized
  coefficient lists and the integer variable `v^r*w`. It gives no result
  for unrestricted rational denominators.

## Formal status

The final Lean build includes twelve standalone files. The target modules
define propositions without asserting them. The separate upstream adapter
was not built against the full original dependency closure. The compiled
object example proves the intended embedded theorem; it is not advertised
as a general mathematical proof compiler.
