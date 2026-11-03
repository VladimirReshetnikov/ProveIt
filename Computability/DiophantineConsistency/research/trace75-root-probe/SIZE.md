# Trace75 first-index and radix size bounds

`Trace75Size.graph_rank_size` is checked in every `IΣ₁` model. For arbitrary
natural ports with beta positive, positive graph witnesses and a zero of the
Lean trace75 ring value, the unscaled first parameter `P=X*Y²` satisfies

```
8*P + 4 ≤ k,       2*q^4 < c.
```

The proof uses the already-checked first Pell index `n≥2`, monotonicity of the
Pell ordinate, and the actual graph's `X=w*q`, `Y=q³*s`. It does not claim
that the odd main index is at least five, establish index alignment, prove
machine halting, or yield an iPRA theorem. External graph/constant binding and
transitive ancestry remain as described in the other trace75 packets.

Accepted source `Trace75Size.lean` SHA-256
`c73f715d65874d5631db65cf7577ca6bea8bde4ce31f7218f1336a4947875932`;
`run-size.py` accepted `observations/size-attempt01/`, object
`/tmp/trace75-size-ogywv9bg/Trace75Size.olean` SHA-256
`2a536f3a3eb2129213dd4b30df564cff717068221c8e7b9b5e864475c29cf058`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
Selected direct providers are pinned; project and package transitive,
historical source/object and dynamic ancestry remain inherited.
