# Independent-y model lemmas and unchecked graph drafts

# Checked generic model lemmas

`IndependentYBounds.lean` passed a guarded Lean check: exit 0, four reports
`[propext, Classical.choice, Quot.sound]`, and no warnings or `sorryAx`.
The [receipt and earlier failed diagnostics](../p64-qcube76-independent-y-guarded-check/README.md#generic-bounds)
record the bounded checks and captured-provider scope. The checked lemmas give
the discrete Pell bound
`c≥2n`, the derived strong-norm bound `f²>c+1`, the auxiliary inequality
`V<y`, and the nonzero old auxiliary root; see the
[mathematical argument](../p64-qcube76-independent-y-analysis/README.md).

# Unchecked graph and witness drafts

The other four Lean files remain **source drafts and have not been checked by
Lean**.
`IndependentYGraphDraft.lean` attempts the new graph's zero-specific residual
split and main Pell-root extraction. `IndependentYSizeDraft.lean` attempts
to apply the generic size inequality to the evaluated strong residual and
main root of an actual 76Y zero. `IndependentYWitnessDraft.lean` attempts
positive model representatives and conditional graph witness maps: the old
signed root must be nonzero, and the new root must strictly exceed evaluated
`V`. Sequential checks require compiled providers for the generated
`P64QCube76Y`, the 77 transport/unit helper, the generic draft, the graph
draft and size draft, as well as the separate ring-binding draft before the
witness draft. `IndependentYJoinDraft.lean` then attempts a positive-zero
equivalence under exactly those two guards. No zero-specific Lean result has
yet discharged them.

Elaboration errors, missing hypotheses and tactic failures remain possible in
those drafts. The generic bounds alone are not a graph equivalence or iPRA
endpoint.
