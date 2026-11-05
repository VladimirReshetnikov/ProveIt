# Model carrier-scale bridge and graph extraction draft

[`FreeMainCarrierScale.lean`](FreeMainCarrierScale.lean) has a clean guarded
[Lean check](observations/scale01/result.json). For every `IΣ₁` model, its
`of_carrier` theorem proves `q ∣ h` from the explicit q-cube scale, positive
`U`, carrier equality and square equation stated in the source. It uses the
separately checked [`FreeMainDivisibility`](../p64-qcube72-model-divisibility-draft/README.md)
lemmas, first obtaining `U∣D`, then `q³∣3h`, then `q∣h`. The output object
SHA-256 is `a7c8af94532cbebfa324e5f95ed2612df43eabc72ffa652e8c880d90a17d211d`.
Lean exited 0, with the expected axiom report, stable direct-input guards, no
warnings or `sorryAx`, and no monitor stop. Direct-input provider ancestry is
inherited transitively, dynamically and between samples.

[`FreeMainGraphDivisibility.lean`](FreeMainGraphDivisibility.lean) is a draft
that would extract those hypotheses from an actual positive 72 graph zero.
Its first guarded [attempt](observations/graph01/result.json) failed with Lean
exit −6 due to the `-M2400` interpreter memory limit; no object or theorem
report was produced. The exact source and log are retained. A graph-specific
`q∣h` theorem is **not yet claimed**. The next step is to split residual
extraction and ring evaluation into smaller modules and avoid expanding a
large polynomial with `linear_combination`, before another resource-coordinated
check.

Neither the checked generic bridge nor the draft proves a 72→76 reverse
witness map, existence equivalence, or an iPRA endpoint. The source comment
calling the generic file unchecked predates its clean check and is preserved
so the source hash matches the receipt.

The extraction has since been split. [`FreeMainGraphShape.lean`](FreeMainGraphShape.lean)
passed its own guarded [shape check](observations/shape01/result.json), proving
the 72 output shape and an arbitrary-ring evaluation formula for the main
residual. Object SHA-256:
`b267810654a87962413aaf1681318b4f57b950d41ead489415033919ddb11ba2`.
The updated graph client imports this shape module and the checked carrier
bridge, and replaces the large `linear_combination` with direct equality
casting. That updated client has **not** been checked; its source differs from
the retained failed graph01 snapshot. Further Lean launches are on hold for
the separate 61-module extension.
