# Conditional clean-predecessor carry reset

`CompactCarryReset.lean` composes the audited heterogeneous end-around carry
theorem with a local predecessor bound in an arbitrary IΣ₁ model. Suppose the
cyclic predecessor's raw column is at most `s+t`, `t≤half`, `s+b<half`, and
`half+half=2^w`, where `b` is the supplied global carry bound. The theorem
proves that the carry entering the target is zero and its output digit is the
target raw column modulo `2^w`. A second theorem says the digit equals that
column if the target raw column is itself below `2^w`.

This provides a conditional arithmetic step suggested by the
[finite fractional-rotation check](../compact44-fractional-clean-column/README.md):
that check gives a temporal predecessor bound for standard finite words. It
does **not** prove this theorem's model-level predecessor decomposition,
the required non-temporal and incoming-carry slack, a target-column bound,
or any graph-specific `CarryInput` hypothesis. No all-model rotation,
machine simulation or iPRA endpoint follows.

Single-side exploratory session 12020 exited 0 without warnings. Both named
axiom reports listed only `propext`, `Classical.choice`, and `Quot.sound`.
The parent object came from the author side of the paired heterogeneous-carry
provider; a coherent paired replay and independent artifact audit of this new
client remain open. See `observation.txt` for the exact command and output.
