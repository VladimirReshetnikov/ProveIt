# `q ∣ h` for every positive 72-graph zero in an `IΣ₁` model

The split client [`FreeMainGraphDivisibility.lean`](FreeMainGraphDivisibility.lean)
now has a clean guarded [Lean check](observations/graph02/result.json). Its
`q_dvd_h` theorem proves, for every positive zero of the generated 72-gate
graph in any `IΣ₁` model and any natural ports,

```
((p 0 : V) * v 0 + 1) ∣ v 13.
```

These are respectively the graph's `q` and free main-gap input `h`. The
client extracts the main residual from the zero, uses the checked
[`FreeMainGraphShape`](FreeMainGraphShape.lean) ring evaluation, and applies
[`FreeMainCarrierScale`](FreeMainCarrierScale.lean). The source comment
calling the client unchecked predates its clean check; source and log are
retained unchanged to match their hashes.

The checked scale bridge proves `q ∣ h` from the explicit q-cube scale,
positive `U`, carrier equality and square equation. It first obtains `U∣D`,
then `q³∣3h`, and uses the separately checked
[`FreeMainDivisibility`](../p64-qcube72-model-divisibility-draft/README.md)
lemma to conclude. That generic lemma uses a split modulo 3 and explicit
Bézout certificates, without a standardness or prime-factorization assumption.

All three checks exited 0 with stable direct-provider guards, no warnings or
`sorryAx`, and no monitor stop:

| Stage | Receipt | Output object SHA-256 |
|---|---|---|
| scale bridge | [scale01](observations/scale01/result.json) | `a7c8af94532cbebfa324e5f95ed2612df43eabc72ffa652e8c880d90a17d211d` |
| graph ring shape | [shape01](observations/shape01/result.json) | `b267810654a87962413aaf1681318b4f57b950d41ead489415033919ddb11ba2` |
| actual-zero client | [graph02](observations/graph02/result.json) | `1f646961efda3232a04ed453729f5d911807dbd2e79c675b472fe93ad79bac33` |

The final theorem reports axioms `[propext, Classical.choice, Quot.sound]`.
The receipts record exact source and provider hashes, commands, resource
samples and logs. Direct-provider guards inherit transitive, dynamic and
between-sample ancestry; these were not rebuilt from source here. The first
[graph01 attempt](observations/graph01/result.json) hit the `-M2400`
interpreter memory limit and produced no object. Splitting the ring shape and
using direct equality casting yielded the successful graph02 check.

This theorem does **not** prove a 72→76 reverse witness map, existence
 equivalence, or an iPRA endpoint. The remaining rank congruence and possible
normalizations are discussed in
[`p64-qcube72-first-index-gap-analysis`](../p64-qcube72-first-index-gap-analysis/README.md).
