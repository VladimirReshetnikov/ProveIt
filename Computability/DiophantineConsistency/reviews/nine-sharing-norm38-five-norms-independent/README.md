# Independent source review of the five-norm draft

The proposed theorem assumes an IΣ₁ model, all four model port-cast
equalities, and a seed zero at distinguished input 1. It rewrites five
individual residual zeros using the already compiled slot identities and
concludes the static `fiveNorms` predicate. The exact mapping is:

| Residual slot | Static target |
| --- | --- |
| 16 | node 61 = 1 (N0) |
| 11 | node 44 = 1 (N1) |
| 27 | node 78 = 1 (Na) |
| 17 | node 66 = 1 (Nt) |
| 28 | node 80 = node 36 (scaled_Ns = Delta) |

This matches `NormAssignment38.fiveNorms`, including its order. The first four
identities have the form `target - 1 = 0`, and the last has the form
`target - Delta = 0`; applying `sub_eq_zero.mp` is mathematically valid in
the difference ring and requires no Delta cancellation. No false statement
was found in this conditional assembly.

`check.py` verifies the pinned draft and five exact slot statements, the
three corresponding previously compiled group objects, and the target order.
It is a source/point-object check, not a Lean parser or proof. The imported
`Norm38EachSlot.each_slot_zero` is required and was not compiled in the
batched run; its later isolated first attempt also failed, so it remains a
pending proof obligation. This five-norm draft itself has not been compiled;
its elaboration, imports and tactics remain unverified. It does not prove
`gatesHold`, source correspondence, reverse construction or iPRA equivalence.
No Lean process was run during this review.
