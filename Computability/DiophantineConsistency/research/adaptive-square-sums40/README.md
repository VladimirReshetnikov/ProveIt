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

**Open:** the 40-variable graph is not yet bound to a Lean literal; its model
equivalence, native iPRA endpoint and guarded replays remain to be established.
There is no global minimality claim.
