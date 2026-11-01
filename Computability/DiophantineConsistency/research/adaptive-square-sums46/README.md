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
other residuals and changes the root residual by `2*(z - psi*t)`.

The Lean `AdaptiveZ46*` modules now bind the exact candidate and parent
literals to a common 33-residual context by definitional equality. In every
IΣ₁ model and for arbitrary integer ports, they derive the root norm and
positive scale quotient from a parent zero, construct the positive oriented
witness, and prove both positive-shift no-zero directions. `verify_literal.py`
checks all 46 inputs and 178 rows against the pinned graph. The paired model
replay matched 12 modules on an accepted historical native-47 provider, with
its actual exit and direct input guards recorded in
`reviews/adaptive-square-sums46-model-replay/`. The no-premise
`IPRAZ46Native.literal_equivalence` endpoint has also passed a matched
14-module [native replay](../../reviews/adaptive-square-sums46-native-replay/README.md).
It concerns the mapped native refutation predicate; its interpretation as
Con(ZFC) uses the separate interpretation and refutation bridge. Project,
package-transitive and dynamic-import ancestry remains inherited, including
the 848-module author-only ancestor. No global minimality is claimed.
