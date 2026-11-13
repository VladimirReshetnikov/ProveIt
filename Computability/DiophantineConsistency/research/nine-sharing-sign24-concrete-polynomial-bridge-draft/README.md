# Sign24 direct polynomial bridge: source-only draft

This proposed client adapts the checked sign25 PolynomialBridge transport
to the Fin24 expression using the proposed sign24/sign25 model-zero
equivalence. It is uncompiled and depends on an as-yet-unchecked expression
equivalence provider and a coherent sign25 provider union. It does not prove
an iPRA endpoint, Lean degree theorem or external byte binding. The separate
sign25 endpoint attempt hit the interpreter memory limit, so the sign24
endpoint cannot be assumed to follow within the existing build limits.
