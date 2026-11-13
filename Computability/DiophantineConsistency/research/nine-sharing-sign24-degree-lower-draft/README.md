# Sign24 exact-degree lower-bound first steps

This source-only draft begins a Lean lower-bound proof for the actual sign24
expression. It identifies the N0 row inside the checked seed and proposes the
commutative-ring identity obtained by setting input coordinate 0 to one,
coordinates 16 and 17 to `t`, and all other seed coordinates to zero:
`N0 = -t^4 - 2t^2 - 1`. A separate generic theorem proposes that the matching
diagonal specialization from 24 variables to one does not increase polynomial
total degree. The input shift changes seed indices 16/17 to direct-expression
indices 15/16.

Neither declaration has been compiled. Even if both pass, they do not prove a
degree-eight lower bound for the full sum of squares: the remaining rows must
be shown not to contribute to the eighth coefficient and the specialized N0
square's leading coefficient must be connected to the actual direct expression.
No JSON/byte or PDF binding follows. Guarded preflight, independent review and
an assigned Lean slot are required.
