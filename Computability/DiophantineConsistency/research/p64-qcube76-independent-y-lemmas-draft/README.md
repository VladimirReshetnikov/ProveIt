# Unchecked independent-y inequality draft

Both Lean files are **source drafts and have not been checked by Lean**.
`IndependentYBounds.lean` attempts to isolate the discrete Pell bound
`c≥2n`, the derived strong-norm bound `f²>c+1`, the auxiliary inequality
`V<y`, and the nonzero old auxiliary root; see the
[mathematical argument](../p64-qcube76-independent-y-analysis/README.md).
`IndependentYGraphDraft.lean` attempts the new graph's zero-specific residual
split and main Pell-root extraction. The latter requires compiled providers
for the generated `P64QCube76Y`, the 77 transport/unit helper, and the first
draft, in that order. It does not yet compose the size, sign, or witness
maps.

The current build occupies the shared Lean slot, so elaboration errors,
missing hypotheses and tactic failures remain possible. These drafts are not
evidence of a proof or an iPRA endpoint.
