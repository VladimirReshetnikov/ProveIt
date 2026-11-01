# Forty-four-variable quartic candidate

This graph replaces both signed positive-coordinate pairs for `W` and the root
skew `Γ` in the 46-variable oriented-root parent by single positive variables.
The pinned circuit has 44 unknowns and 176 live operations. `generate.py`
checks the replaced parent gates and graph liveness; `verify_degree.py` checks
that all 33 residuals are quadratic and their sum has exact degree four.
`verify_substitution.py` checks all parent residuals under the forward
embedding `(wPositive,wNegative)=(W+1,1)` and
`(rootSkewPositive,rootSkewNegative)=(Γ+1,1)`.

The reverse direction needs positivity of the original signed `W` at every
positive parent zero. The Lean proof uses its first norm: if `W≤0`,
the root-skew constraint gives `Γ=kW`, and the root equation forces the
positive first root to be at least `psi*(ell+k)`. Its norm and the positive
scale instead give `Z=psi*t` with `t<ell+k`. The general IΣ₁ inequality
`ArithmeticAdaptiveTransport2011.first_root_bound` supplies the last bound.
`AdaptiveZ44PositiveActual` proves this positivity and the ensuing `Γ>0`
from the actual residuals; `AdaptiveZ44Model.shifted_no_zero_iff` then proves
the 44-to-46 no-zero equivalence in every IΣ₁ model for **all natural port
vectors**, without assuming a port is positive. The exact graph is bound to
the Lean literal, and the [paired model replay](../../reviews/adaptive-square-sums44-model-replay/README.md)
matched all seven modules on a historical native-46 provider.

The no-premise `IPRAZ44Native.literal_equivalence` endpoint also has a
[matched nine-module replay](../../reviews/adaptive-square-sums44-native-replay/README.md),
using the existing `currentPorts_cast` theorem to specialize the all-natural-
port model equivalence to the fixed integer ports. It concerns the mapped
native refutation predicate; its interpretation as Con(ZFC) uses the separate
interpretation and refutation bridge. The replays inherit project,
package-transitive and dynamic-import ancestry, including the author-only
848-module ancestor; they are not a complete current-source closure. No global
minimality is claimed.
