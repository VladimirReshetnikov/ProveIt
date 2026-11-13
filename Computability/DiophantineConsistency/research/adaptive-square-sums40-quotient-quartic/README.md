# Candidate: 40-variable quartic with both scaled-root quotients

Starting from the 41-variable quartic, replace its positive main root `D` by a positive
quotient `s`, reconstructing `D=mainScale*s`. Replace the main norm residual
`D²-mainScale²*(1+deltaProduct)` by `s²-(1+deltaProduct)`, and replace the root
binding residual by `mainScale*s-DstarComputed`. Remove the redundant positive
`varphiSquare` variable and its defining residual. The resulting graph has 40
positive inputs, 166 live arithmetic rows and 31 squared residuals.

`verify_substitution.py` checks the exact parent-to-child residual identities
under `D=mainScale*s` and `varphiSquare=mainScale²`: 30 residuals agree, the
old main norm is `mainScale²` times the new norm, and the removed definition
vanishes. `verify_degree.py` checks all new residuals are quadratic and proves
exact quartic degree using sparse integer-polynomial arithmetic. These finite
checks are not Lean model or native iPRA theorems.

A positive child witness embeds into the parent using the displayed
reconstruction. For a positive parent zero, the checked `scaled_quotient`
theorem gives an integral `s` with `D=mainScale*s` and the reduced norm, and
positivity of D gives `s>0`. Both model witness maps and the native iPRA
endpoint have now compiled in an [incremental author-side run](../../reviews/adaptive-qm40-native-incremental-author/README.md).
The [standard-presentation client](../ipra-standard-qm40/author-rebuild/README.md)
also compiled in an author-side extension. The paired replay and formal PDF-byte
binding remain open. No global minimality is claimed.
