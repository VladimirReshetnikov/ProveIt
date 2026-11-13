# Trace75 first index at least two

`Trace75Index.first_index_ge_two` is checked in every `IΣ₁` model. For arbitrary
natural ports with `0<beta`, positive graph witnesses and a zero of the Lean
trace75 value in the difference ring, **every** `n` satisfying the first
Pell ordinate equation

```
2*ycoord n (2*(X*Y²-1)+1) = k
```

satisfies `2≤n`. It combines the odd main ordinate already obtained by the
noncircular fold with the generic first-index-one interval contradiction,
specialized to the unscaled trace75 main base `Y*(X+1)`. It proves neither a
main-index bound nor index alignment, halting or iPRA; JSON/payload binding
is external.

Accepted source `Trace75Index.lean` SHA-256
`96c530584c25b72f4887f57f371b3cd6602fb5fd018c98faa47ab88b55e801ee`;
`run-index-v2.py` accepted `observations/index-attempt02/`, object
`/tmp/trace75-index-ri6h6wbv/Trace75Index.olean` SHA-256
`6cc75eb28726516d4901542f26f083ecceeb682d459ff4a71022f3d88b1a3a34`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
The first failed attempt and snapshot are retained. Selected direct providers
are pinned; transitive project/package, historical source/object and dynamic
ancestry remain inherited.
