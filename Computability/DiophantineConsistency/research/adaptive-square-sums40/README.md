# Forty-variable degree-six candidate

This 160-operation graph starts from the 42-variable degree-six parent. It
substitutes the positive linear expression `productVariable2 + Y` for
`aVariable` and replaces the two signed-`Q` coordinates by one positive
`qValueVariable`. The parent’s strong-square residual suggests the reverse
direction: at a zero, signed `Q` equals the square of the positive scaled-index
coordinate. The construction removes one residual square, one accumulation
gate and the signed subtraction gate.

`generate.py` pins and checks the parent rows and checks the resulting graph's
liveness and topological order. `verify_substitution.py` checks all 28 parent
residuals as exact sparse integer polynomials under the forward substitution
`qPositive = qValueVariable + 1`, `qNegative = 1`; the removed residual becomes
zero. `verify_degree.py` establishes exact degree six by finite computation.
These calculations do not prove the reverse zero-set implication in all models.

The exact graph is bound to a Lean literal by `AdaptiveAQ40Literal.literal`,
and `AdaptiveAQ40.shifted_no_zero_iff` proves its no-zero equivalence to the
42-variable parent in every IΣ₁ model for arbitrary integer ports. Its
[paired model replay](../../reviews/adaptive-aq40-model-replay/README.md)
matched eight modules on a historical provider. Its no-premise
[native endpoint](../../Lean/DiophantineConsistency/IPRAAQ40Native.lean)
has a [matched ten-module replay](../../reviews/adaptive-aq40-native-replay/README.md).
It refers to the mapped Foundation refutation predicate; identifying that
predicate with Con(ZFC) uses the separate interpretation and refutation bridge.
Historical project, package-transitive and dynamic-import ancestry remain
inherited. There is no global minimality claim.

The [base-10 equation presentation](../../equation6-40.pdf) has separately
named positive variables. `generate_equation6_40.py` creates the TeX and
`verify_display6_40.py` checks its 44 definitions, 27 residuals, 160 gates,
fixed constants and mutation controls. Two clean PDF builds matched SHA-256
`39da58890093f348f0ba9354f14805567293ac1292195ddac568195cd4b6a686`.
