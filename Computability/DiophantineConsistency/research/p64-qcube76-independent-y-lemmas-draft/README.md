# Unchecked independent-y inequality draft

All four Lean files are **source drafts and have not been checked by Lean**.
`IndependentYBounds.lean` attempts to isolate the discrete Pell bound
`c≥2n`, the derived strong-norm bound `f²>c+1`, the auxiliary inequality
`V<y`, and the nonzero old auxiliary root; see the
[mathematical argument](../p64-qcube76-independent-y-analysis/README.md).
`IndependentYGraphDraft.lean` attempts the new graph's zero-specific residual
split and main Pell-root extraction. `IndependentYSizeDraft.lean` attempts
to apply the generic size inequality to the evaluated strong residual and
main root of an actual 76Y zero. `IndependentYWitnessDraft.lean` attempts
positive model representatives and conditional graph witness maps: the old
signed root must be nonzero, and the new root must strictly exceed evaluated
`V`. Sequential checks require compiled providers for the generated
`P64QCube76Y`, the 77 transport/unit helper, the generic draft, the graph
draft and size draft, as well as the separate ring-binding draft before the
witness draft. No zero-specific Lean result has yet discharged the two
conditional witness-map premises.

The current build occupies the shared Lean slot, so elaboration errors,
missing hypotheses and tactic failures remain possible. These drafts are not
evidence of a proof or an iPRA endpoint.
