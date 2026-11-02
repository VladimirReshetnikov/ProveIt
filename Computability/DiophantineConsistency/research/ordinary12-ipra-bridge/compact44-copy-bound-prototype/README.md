# Exploratory model 41-bit copy bound

For any `IΣ₁` model `V`, `CompactCopyBound.copy_bound` proves that if the
41 externally indexed model values `bits : Fin 41 → V` each satisfy
`bits i ≤ 1`, then their model-valued weighted sum satisfies

```
∑ i : Fin 41, 2^i * bits i < Exp.exp 41.
```

The strict bound is the `W<2^41` hypothesis needed by
`Compact943Decoder.decode_iff`. The separate `model_bit_copy_bound` corollary
uses the already-proved `fbit_le_one` for an arbitrary model word and arbitrary
41 model-valued positions. Neither theorem identifies those bits with the
copy digits of a graph word or its weighted sum with a graph column. To apply
the decoder one must still prove the selector and copy Boolean/word
identities appropriate to the construction and provide its local `NoCarry`
premise. No retained-port binding, word/rotation transport, machine
correctness or internal iPRA theorem follows.

Single-side exploratory session 94883 actually exited 0 without warnings;
both named reports were `[propext, Classical.choice, Quot.sound]`. The source
was compiled against the author side of the independently reviewed
same-witness saturation provider; the command, object hashes, exact output,
and terminal observations are recorded separately. This is not a fresh
source-frozen paired replay or independent artifact audit.

The uncompiled `compact44-next-drafts/CompactCopyBound.lean` was used as the
starting point. Its exact copied source and the compiler output of session
81146 are retained under `observations/attempt01`: that run exited 1 because
`Nat.cast_sum` was unavailable in this model context and its reports contain
`sorryAx`. The successful source proves the needed finite natural-cast sum
identity directly by standard `Finset` induction instead. The failed report
is not proof evidence.
