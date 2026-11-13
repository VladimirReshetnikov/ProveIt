# Independent source review: natural-80 Lean transcription

The [source draft](../../research/ordinary14-natural-forced-gamma80-lean-draft/README.md) matches the pinned 80-operation JSON graph at the source-text level. The independent checker reconstructs the entire Lean file byte for byte from that graph and a fixed template, rather than using the author's parsing procedure. It checks the 14 input slots and four symbolic port slots, every ordered graph operation, all ten selected fields, topology and liveness, and the product shape stated by `output_shape`.

This is not Lean elaboration or a theorem about the semantics of the JSON or source file. The proposed `rfl` proof and `#print axioms` command have not been run. The checks do not prove the gamma-positivity model argument, symbolic-port-to-physical-byte equality, PDF binding or iPRA derivability.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural-forced-gamma80-lean-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural-forced-gamma80-lean-independent/result.json
```
