# Independent source review: natural-81 Lean transcription

The [source draft](../../research/ordinary14-natural-forcedj81-lean-draft/README.md) matches the pinned 81-operation JSON graph at the source-text level. The independent checker reconstructs the entire Lean file byte for byte from that graph and a fixed template, rather than relying on the author's parser. It verifies the 14 input slots and four symbolic ports, every ordered graph operation, all ten selected fields, topology and liveness, and the product shape asserted by `output_shape`.

This is not Lean elaboration or a theorem about the semantics of either the JSON or the file. The `rfl` proof and `#print axioms` command have not been run. The checks do not establish the external zero-existence argument in a model, symbolic-port-to-physical-byte equality, PDF binding or iPRA derivability.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural-forcedj81-lean-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural-forcedj81-lean-independent/result.json
```
