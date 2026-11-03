# Exact nonnegative offset after index alignment

`Direct80OffsetExact.graph_offset_exact` proves in every IΣ₁ model that an actual positive 80-graph zero under the explicit positive/odd beta and low/high port bounds has a positive first index `n` and natural `s` with `2n=rankNat+1`, `k=rankNat+1+4*firstParam*s`, and exact signed graph offset `e=ι(4*firstParam*s)`. The proof uses the **full** first Pell recurrence residue after, rather than before, the independently established exact alignment. In particular, it derives nonnegativity of `e` instead of assuming its sign.

`graph_offset_full_divisibility` further derives the stronger signed divisor `(μ²Y²) ∣ e` in the model difference ring, using the exact graph identity `firstParam=X*(μY)²`. This is stronger than the earlier μ²-only cancellation and preserves the actual Y factor; it assumes no coprimality of Y and h.

Guarded author `observations/attempt02/` passed without diagnostics, yielding `/tmp/tenpositive-80offset-exact-qybcyxo0/Direct80OffsetExact.olean`, SHA-256 `448c0384dcaaa704605d64e1caa3cbe714446745bee4e283af24f7b647ec04a7`; attempt01 checked the earlier one-theorem source. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. Selected prototype objects and one inherited provider are pinned, not the complete project/package/dynamic or historical source-object ancestry. Resource checks are sampled; no paired replay is claimed.

The fixed-port hypotheses, remaining source reconstruction, graph-to-halt theorem and iPRA endpoint remain separate.
