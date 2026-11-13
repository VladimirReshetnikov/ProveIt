# Independent source review: 78-operation auxiliary-root Lean graph

**Source review passes; not elaborated.** The proposed source is the literal
78-row graph generated from the reviewed auxiliary-root candidate. Its 14
input slots and four integer ports match the candidate, with slot 8 the
direct first Pell root and slot 11 the direct auxiliary root. The exposed
output is grouped as five residual squares. This is source generation, not a
Lean theorem about an external JSON file or its operation count.

The checker independently compares every generated `let` row with the
pinned candidate, verifies the slot and port declarations and output-field
shape, reruns the graph generator in check mode and replays the candidate's
external checker. These are text and external arithmetic checks only. No
Lean process is run; parsing, `rfl`, reduction/resource behavior, source and
object provider ancestry, graph-to-model bridges, file semantics and the
iPRA endpoint remain unverified.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary14-aux-root78-lean-draft-independent/check.py
```

Compare stdout with `result.json`.
