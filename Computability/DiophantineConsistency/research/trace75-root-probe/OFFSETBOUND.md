# Trace75 signed offset estimate

`Trace75OffsetBound.graph_offset_bound` is Lean checked in every `IΣ₁` model.
For arbitrary natural ports with beta positive and ten positive inputs, it
proves in the model's difference ring

```
2*e < V²*D,   D = X*Y,
```

where e and V are the actual signed trace75 graph registers. No graph zero or
sign of the transport B is assumed. The proof uses the unsquared trace
`V=F*b-c`, the actual denominator D=XY≥2, and a generic ordered-ring offset
lemma. This necessary estimate alone does not prove B≥0/C>0, a halt/iPRA
equivalence, a trace74 guard, or JSON/payload binding.

Accepted source `Trace75OffsetBound.lean` SHA-256
`2d26532cb6d7ca1e7cc323d9a3378ea42a9f7ea701bb1e487588c073f74966f8`;
`run-offsetbound-v2.py` accepted `observations/offsetbound-attempt02/`, object
`/tmp/trace75-offsetbound-6cyh823t/Trace75OffsetBound.olean` SHA-256
`ff61154c7dfec50724c92d55a95b3610d41bccb8c294b02b0a888ef4db11236b`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
The first attempt failed on a missing historical 80-module dependency and is
retained. The accepted attempt uses the separate fresh generic transport
rebuild. Direct providers are pinned; project/package transitive, historical
source/object, between-stage and dynamic ancestry remain inherited.
