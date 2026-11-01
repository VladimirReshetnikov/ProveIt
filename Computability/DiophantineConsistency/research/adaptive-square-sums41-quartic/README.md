# Candidate: 41-variable quartic with a first-root quotient

The [base-10 display](../../equation4-41.pdf) is a conditional candidate, not yet a new consistency endpoint. Starting
from the 42-variable quartic, replace its positive first root `Z` by a positive
quotient `t` (shown as `z` in the display), reconstructing `Z = scale*t`. Replace the first norm residual
`Z² - scale²*(1+ellProduct)` by `t² - (1+ellProduct)`, and replace the root
binding residual by `scale*t - ZComputed`. The now-redundant positive
`psiSquare` variable and its defining residual are removed. The resulting
graph has 41 positive inputs, 170 live arithmetic rows and 32 squared
residuals.

`verify_substitution.py` checks the exact parent-to-child residual identities
under `Z=scale*t` and `psiSquare=scale²`: 31 residuals agree, the old first
norm is `scale²` times the new norm, and the removed definition vanishes.
`verify_degree.py` checks every new residual is quadratic and proves exact
quartic degree by sparse integer-polynomial arithmetic. These are finite
checks, not Lean model or native iPRA theorems.

A positive child witness embeds into the parent using the displayed
reconstruction. For a positive parent zero, the already checked
`ArithmeticAdaptiveQuotients2011.scaled_quotient` gives an integral `t` with
`Z=scale*t` and the reduced norm, provided the positive scale and old square
identity are bound to the literal residuals. The quotient is positive because
`Z` and `scale` are positive. Binding these facts to the full graph, both
witness maps, and the native endpoint remains open; the candidate's exact
fourth degree does not establish zero-set equivalence or global minimality.
