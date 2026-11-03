# Restricted 73/75 positive-zero equivalence

`Trace73RestrictedIff.restricted_iff` proves, in every supported IΣ₁ model and for the same four natural ports, an equivalence between:

* a positive 75-row zero whose same-valuation shift obeys `0 ≤ V² B < ι(n)`; and
* a positive literal 73-row zero whose same-valuation shift obeys `0 ≤ V² B`.

The proof constructs the witness in each direction using the exact all-ring substitution. It uses the model difference ring's nonnegative-cone representation, and establishes that the shift is unchanged when only slot 7 is updated. The inequality on the 75 side supplies the positive center; the 73-side nonnegative shift makes the lifted 75 witness positive.

These are restrictions within the two existentials. This theorem does not prove them for arbitrary zeros, does not establish unrestricted 73/75 equivalence, and does not give an iPRA result for 73. The literal Lean rows were compared to JSON by a separate external checker; file semantics are not formalized.

The guarded author check in `observations/attempt01/` and its outer runner exited 0 with no warnings or errors. Its axiom report is retained there. The result `/tmp/trace73-iff-00auoa1w/Trace73RestrictedIff.olean` has SHA-256 `f328387a531b858239b7ebb452c9b50535417051b603910f3822f9f63659fe45`. Direct imports and selected predecessor objects are pinned by the runner; full transitive project/package/dynamic ancestry remains inherited and no independent replay is claimed.
