# Independent source review: natural-79 Lean graph draft

The [proposed Lean source](../../research/ordinary14-natural-forced-w79-lean-draft/README.md) is a faithful text transcription of the pinned [79-operation external graph](../../research/ordinary14-natural-forced-w79/README.md). This is source correspondence only: the module, its claimed output shape and expression semantics have not been elaborated in Lean, and no iPRA, coefficient-byte or PDF binding follows.

The deterministic receipt reconstructs the whole source byte-for-byte from the candidate JSON, including the fourteen ordered input aliases, four symbolic ports, all 79 gate rows and operands, the ten exposed fields, and the proposed product shape. It independently checks graph topology and liveness. It additionally compares the entire source with the pinned natural-80 draft: after renaming the namespace, exactly the `w=n_w+1` node is deleted and its only consumer is changed from `q*w` to `q*n_w`.

The reconstruction checker is adapted from the earlier [natural-80 independent source checker](../ordinary14-natural-forced-gamma80-lean-independent/check.py); it is a distinct replay of the new input and source, not a separate Lean implementation. It does not establish Lean parsing, typing, theorem axioms or model-zero equivalence.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural-forced-w79-lean-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural-forced-w79-lean-independent/result.json
```
