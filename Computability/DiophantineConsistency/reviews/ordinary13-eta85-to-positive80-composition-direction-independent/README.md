# Independent review of conditional 85-to-positive-80 composition

This reviews source statements and application directions in
`research/ordinary13-eta85-to-positive80-composition-draft/`; no Lean or
provider build was run. The receipt pins the proposal, its author receipt,
and the directly named source interfaces.

The proposition `polynomialBridge85` starts with an explicit
`PolynomialBridge` for `positiveShift` of the exact generated positive-80
graph at `ports K`. Its successive cited source signatures have the matching
input/output direction: positive-shifted 80 → natural 89 → natural 88 →
natural 87 → natural 86 → eta-natural 85. All five use the same compact port
tuple. The first step supplies its direct-coordinate replacement by composing
the separate proposed `DirectFY` and `RReplacement` clients. The final step
supplies the proposed `ForcedEta` wrapper. The separate `native85` theorem
uses that same exact positive-80 premise and passes the eta wrapper to the
previous conditional native client.

There is one explicit mathematical premise in these declarations. This is
not evidence that the remaining dependencies are checked: source-level
proofs of factor extraction, root replacement, gamma/w/J transports, eta
parity, model reflection, imports and provider/axiom ancestry all remain
unelaborated. The exact positive-80 bridge itself remains a premise. No fixed
K endpoint, physical coefficient/PDF connection, or equivalence with the
user's ZFC consistency sentence is established by this composition review.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-eta85-to-positive80-composition-direction-independent/check.py
```
