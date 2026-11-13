# Actual-port rational evaluator: external zero equivalence

`actual_rational_zero_iff` proves that, at the actual fixed current14
integer ports, the 64-row fixed-rational-leaf evaluation has a strictly
positive integer zero iff the current14 integer syntax has one. Both
directions use the same 14-coordinate integer valuation. It combines the
checked arbitrary-port rational specialization with the independently
checked nonzero-beta theorem for the actual ports.

This is an **external Lean proposition** about ordinary integer and
rational evaluations. It does not construct a rational-leaf object-language
sentence or an iPRA derivation of one. The current14 iPRA theorem is a
separate theorem about integer syntax. Rational leaves use a different
operation-count convention, so this does not establish an integer-leaf
64-operation equation or change the maintained equation/PDF.

The guarded check passed: Lean and runner exit 0, no warnings or `sorryAx`,
with axiom report `[propext, Classical.choice, Quot.sound]`. It ran for
1.638 seconds, peak sampled group RSS 1,927,667,712 bytes, under `-M2400`,
120 seconds, 3.5 GiB group RSS and 10 GiB available-memory limits, nice 19
and idle I/O. Both direct predecessor objects, their receipts and base
state were pinned and stable. Transitive/dynamic ancestry and sampling
remain limitations. The output object is
`/tmp/rational-carrier64-current14-actual-external-priority-check01/RationalCarrier64ActualExternal.olean`,
SHA-256 `1486ef0d67c262527bd3cab26f6d0bfe4749fcfd8b9d068e3018c61dec1fa93c`.

| Artifact | SHA-256 |
| --- | --- |
| `RationalCarrier64ActualExternal.lean` | `2be98d8369526bfca5039939ef6f9f3384a68cd7d267afac7647eb224e5e03bd` |
| `check01.py` | `b60a19463d05f9d32ad52cc4f7ece165e4dd58afa59e9843e2432378b9677e72` |
| `observations/attempt01/compile.log` | `76656fb2fdbdd287f2003867091c95ba3b0f0ab4f070790b06240e202c94a0c3` |
| `observations/attempt01/result.json` | `b876bd365509fe34f4234b0f23d62eb0ba63acc7124a7b4c38b389717c7d63f7` |
