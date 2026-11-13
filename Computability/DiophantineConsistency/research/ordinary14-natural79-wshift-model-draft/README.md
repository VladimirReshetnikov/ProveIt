# Natural-79 to natural-80 w shift: source-only model proposal

`Natural79WShift.lean` proposes a ring identity and related-valuation model
transfer for the independently reviewed [79-operation graph](../ordinary14-natural-forced-w79/README.md)
and its [80-operation parent](../ordinary14-natural-forced-gamma80/README.md).
This is **unelaborated source**: no Lean parser, compiler, model proof, axiom
report, iPRA endpoint or physical coefficient/PDF binding is established. The
literal 79/80 graph modules and the arithmetic/model providers are also
unelaborated for this proposed chain.

An [independent source and mathematical review](../../reviews/ordinary14-natural79-wshift-model-independent/README.md)
checks the graph edit, witness directions and explicit positivity premise;
it does not elaborate the model declarations.

The ring statement compares the 79 graph at valuation `v` with the 80 graph
at the valuation `down80 v`, which subtracts one from **slot 6 only**. It is
not equality at the same valuation. The exact external graph delta deletes
`w=n_w+1` from the 80 graph and substitutes `n_w` at its consumers; every
other row agrees. That proves the changed-valuation polynomial identity by
structural congruence over a commutative ring, assuming the mathematical
interpretation of the pinned literal graphs. The source proof proposes a
`simp` tactic for this identity; its elaboration and resource use have not
been checked.

The proposed model relation instead uses natural-model witnesses `v79` and
`v80` satisfying `v79 6=v80 6+1`, with all other coordinates equal. The
source proposes converting this relation, via `ModelDifferenceRing`, into
`InternalZero` equivalence. It then proposes equivalence of *existence* of
zeros **only with the explicit assumption**

```
∀ v, InternalZero (P79NaturalForcedW.graph p).output v → 0 < v 6.
```

The 79-to-80 direction obtains a predecessor from that assumption and
explicitly commutes the successor witness with `add_comm`. The reverse
witness increments slot 6. The source does **not** establish the positivity
hypothesis for any selected ports. The external forced-w proof uses
`beta>0`, `K0>=0` and a separate zero-specific factor and divisibility
argument; its model formalization and the stronger inherited parent endpoint
conditions are not supplied here. The positivity premise cannot be erased
merely from the ring identity or from an external finite test.

The read-only checker pins both JSON graphs, both literal graph source drafts,
the model interface and this client source. It compares every literal graph
row and input/port alias to JSON, verifies the one-gate DAG edit exactly,
checks the related-valuation and conditional-existence source signatures, and
runs 300 finite modular controls. Those controls supplement the unbounded
structural identity but cannot validate a Lean theorem or model witness. The
three `#print axioms` commands are source text and have not been executed.

Run from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary14-natural79-wshift-model-draft/check_source.py | cmp - research/ordinary14-natural79-wshift-model-draft/result.json
```
