# Opposite-direction 79 gauge obstruction

`Mask79NegativeObstruction.negative_guard_sum` proves in every supported IΣ₁ model, for arbitrary natural ports/valuations and model-natural `t`, that if `b*t≤F`, then

```text
(F−b*t) + (C+q*b*t) = (F+C)+b²*t.
```

Thus `no_negative_guard` shows an initially unguarded valuation stays unguarded under the opposite-sign gauge update, provided the subtraction bound holds. Positivity of the moved F coordinate implies that bound. Together with the separately checked [nonnegative-direction obstruction](../ten-positive-79-gauge-guard-obstruction/README.md), this blocks using either sign of this gauge update to normalize an unguarded positive valuation, subject to relating a signed ring parameter and the corresponding model-natural coordinates. This packet does not yet prove that combined signed-ring statement. It neither proves existence of an unguarded positive graph zero nor decides unrestricted 79/80 equivalence; a different transformation remains possible.

Guarded author `observations/attempt01/` and its enclosing tool session exited 0. Source SHA-256 is `5c7491c087334609b7fb730c79322684a5f895768bd6d2a81945f789869d53e3`; terminal SHA-256 is `c5f345448d43f421827e3679059306408eafab8f2d1879cc4b228837129dd8c4`; output `/tmp/mask79-negobstruction-131xhpwn/Mask79NegativeObstruction.olean` has SHA-256 `9846a812aef9268f5bdf6fada2cc5e5aed25538b509333f7dcabff566b01838f`. The direct natural-lift and selected predecessor objects are pinned; full historical project/package/dynamic ancestry remains inherited. No independent Lean replay or external file semantics is claimed.

**Later result:** the [signed-gauge obstruction](../ten-positive-79-gauge-signed-obstruction/README.md) proves that the exact corrected gauge cannot turn an unguarded valuation with positive F into a guarded model-natural valuation for either sign of its difference-ring parameter. This does not decide unrestricted 79 equivalence or rule out another transformation.
