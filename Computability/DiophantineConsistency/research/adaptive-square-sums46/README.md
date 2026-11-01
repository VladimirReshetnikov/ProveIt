# Forty-six-variable quartic orientation candidate

This graph replaces the parent 47-variable positive pair `zPositive`,
`zNegative`, whose difference is the signed root `Z`, by one positive
`zValueVariable`. It has 46 unknowns and 178 live operations. `generate.py`
pins the parent and checks the changed bindings, liveness and gate order.
`verify_degree.py` checks all 33 residuals have degree at most two and certifies
that their sum of squares has exact degree four. `verify_substitution.py`
checks the forward embedding `zPositive = zValueVariable + 1`,
`zNegative = 1` for all 33 residuals using exact sparse polynomials.

The proposed reverse orientation uses special structure, not a bare direct
substitution. At a parent zero the residuals give
`Z² = psi² * (1 + tau)` and `psi > 0`, so the positive magnitude `z = |Z|`
is nonzero and has the form `z = psi * t` for a natural `t`. The repository's
`ArithmeticAdaptiveQuotients2011.scaled_quotient` proves the corresponding
square-divisibility result in every IΣ₁ model. The witness `r` occurs only in
the computed root with coefficient `psi`. If the old signed `Z` is negative,
replace it by `z` and increase `r` by `2*t`; otherwise leave `r` unchanged.
`verify_orientation.py` checks exactly that this transformation preserves all
other residuals and changes the root residual by `2*(z - psi*t)`. This is a
polynomial identity, not a Lean proof that its quotient and positivity
hypotheses hold at a parent zero.

**Open:** the candidate is not yet bound to a Lean literal, and the conditional
orientation, arbitrary-model positive witness maps, no-zero equivalence,
native iPRA endpoint and guarded replays still need proofs. No global
minimality is claimed.
