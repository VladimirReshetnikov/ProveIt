# Source-only Lean transcription of the natural 79 graph

`P79NaturalForcedW.lean` is an **uncompiled draft** of the literal
[79-operation, degree-107 natural-input graph](../ordinary14-natural-forced-w79/README.md).
It retains fourteen input slots and four symbolic integer ports in the JSON
order, exposes five unit factors and selected intermediates, and proposes an
`output_shape` proof. The source is adapted from the 80 graph by removing the
`w` shift and using the natural input directly; no Lean proof has been run.

The deterministic checker pins the candidate JSON and Lean source, compares
all 79 ordered rows and operands, checks input and port slots, topology,
liveness, exposed fields and the stated product shape. This is source-text
correspondence, not a Lean elaboration or a theorem of semantic equivalence,
iPRA derivability, external byte binding or PDF interpretation.

An [independent source review](../../reviews/ordinary14-natural-forced-w79-lean-independent/README.md)
reconstructs the graph and checks the complete source delta without running Lean.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary14-natural-forced-w79-lean-draft/check.py | cmp - research/ordinary14-natural-forced-w79-lean-draft/result.json
```
