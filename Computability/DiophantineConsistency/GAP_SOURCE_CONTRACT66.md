# H2082 carry, source and finalizer contract

`GapSourceCarry66` instantiates the existing two-block sparse carry theorem
with low length117 and high length2083. Its product-degree bound follows
from the three H2082 degree ceilings and the maximum input weight116.
The coefficient magnitude bound is derived from the existing generic
31-coordinate convolution estimate and `B>=4096*H*b^2`. No per-assignment
coefficient, degree or no-carry certificate is assumed.

`tau_targets_iff` identifies the zero carry test with an explicitly supplied
bounded natural digit vector, its actual sparse encoding, and vanishing of
all monitored target coefficients. Kernel height and high-word nonnegativity
remain explicit in this generic theorem.

`GapSourceContract66.binomial_iff_source` then discharges those word, degree,
coefficient and mask-calibration conditions from `GapSourceWords66.Valid`.
For `b=2^k` and the weak cap `g<4*b*B^116`, the exact central-binomial
threshold test is equivalent to

```
exists z : Fin31 -> Nat,
  (forall i, z_i < b) and
  g = indexedCode B weights z and
  (forall target, coefficient(sourcePolynomial z,target) = 0).
```

The mask population is derived from the actual31 low positions and22 target
positions. It is not an assumed numerical calibration equation.

`source_of_zero` first applies the checked H2082 ratio soundness theorem.
A positive final-equation zero recovers the power-of-two base and weak cap,
then decodes the bounded source coordinates. Conversely, `zero_of_source`
uses a bounded source vector with the stronger code cap `g<b*B^116` to
construct positive free-carrier coordinates and a positive final coordinate.
The subsequent [cofinal-existence stage](GAP_SOURCE_NINE66.md) supplies that
stronger code cap explicitly and removes the digit bound.

The source coefficients are the explicit three-channel product. For the
literal H2082 parameters, `GapKernels66.sourcePolynomial_zero_iff` already
identifies their target zeros with `GapSource66.rows`. This stage makes no
whole-tuple native compiler calibration or object-language ZFC claim.

Dedicated checks audit all three carry endpoints and all three contract
endpoints. Only Lean's standard axioms occur.
