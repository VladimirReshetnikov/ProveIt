# Positive 80 unit product to positive 81 four squares

This is an **unelaborated source-only model transfer**, not a checked
`PolynomialBridge` or iPRA endpoint. The exact positive-81 graph is generated
from the pinned 81 JSON with its four residual fields, and the positive-80
graph comes from the separately generated exact unit-product literal. Both
have the same witness order and four integer port expressions.

The first 73 source rows are identical. The 81 output is
`A0²+A1²+(Fa−1)²+g72²`; the 80 output is
`(1+A0)*(1+A1)*Fa*(1+g72)−1`. The 81-to-80 proposed direction extracts
vanishing residuals from a sum of nonnegative model-ring squares and is
stated at arbitrary natural valuations. For the other direction, positive
80 inputs are lowered at the ten shifted coordinates to an exact 89 zero,
then mapped forward through the already drafted J/gamma/w/eta shifts to the
actual 85 prototype. The prototype's own signed unit-factor bridge proposes
that its four residuals vanish. The new source proposes exact identities
binding those four prototype residual values back to the *same* positive
80/81 valuation. This direction explicitly requires every parent coordinate
positive; it does not assume a reverse root switch, eta forcing, positive
beta, or a fixed port tuple.

The two directions are then applied to `positiveShift` at the same arbitrary
integer port tuple. `bridge80` retains the exact positive-shifted **81 parent
PolynomialBridge** as a hypothesis. The final proposed 85 native client
specializes both graphs to the same compact `ports K` and composes the prior
85→80 source; its explicit premise is the exact 81 parent bridge. All 85
factor/zero-map/parity/root-switch proofs, the selected natural-to-integer
model casts, graph field normalization and nonnegative-square arguments,
fixed K/byte/PDF association, provider closure and axiom reports remain
unverified. No claim is made that the 81 parent bridge or final iPRA/ZFC
equivalence has been proved.

From `Computability/DiophantineConsistency` run
`python3 -I -S -B research/ordinary13-positive80-to81-model-draft/check.py`
and compare with `receipt.json`. It regenerates the 81 literal in a temporary
tree, checks the full shared prefix/finalizer and bounded factor/shift
identities. It does not run Lean or stage artifacts.
