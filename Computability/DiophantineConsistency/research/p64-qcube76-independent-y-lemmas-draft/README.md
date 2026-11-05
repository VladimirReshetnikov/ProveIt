# Checked independent-y model lemmas

# Checked generic model lemmas

`IndependentYBounds.lean` passed a guarded Lean check: exit 0, four reports
`[propext, Classical.choice, Quot.sound]`, and no warnings or `sorryAx`.
The [receipt and earlier failed diagnostics](../p64-qcube76-independent-y-guarded-check/README.md#generic-bounds)
record the bounded checks and captured-provider scope. The checked lemmas give
the discrete Pell bound
`c≥2n`, the derived strong-norm bound `f²>c+1`, the auxiliary inequality
`V<y`, and the nonzero old auxiliary root; see the
[mathematical argument](../p64-qcube76-independent-y-analysis/README.md).

# Graph, witness and join status

`IndependentYGraphDraft.lean` passed a [guarded check](../p64-qcube76y-graph-model-guarded-check/README.md)
of the new graph's zero-specific residual split and main Pell-root extraction.
`IndependentYSizeDraft.lean` also passed a [guarded check](../p64-qcube76y-size-guarded-check/README.md)
of the actual-zero bound `f²>c+1`. `IndependentYWitnessDraft.lean` passed a
[guarded check](../p64-qcube76y-witness-guarded-check/README.md) of positive
model representatives and both conditional graph witness maps. The two
zero-specific premises have been checked separately in the
[old-root](../p64-qcube76y-oldroot-guarded-check/README.md) and
[strict-root](../p64-qcube76y-strict-guarded-check/README.md) packets.
`IndependentYJoinDraft.lean` and the full unconditional join now pass their
[guarded checks](../p64-qcube76y-join-guarded-check/README.md).

The resulting all-model positive-zero equivalence is checked. The separate
[iPRA endpoint client](../p64-qcube76y-ipra-guarded-check/README.md) has also
passed its guarded check; external file/PDF binding remains separate.
