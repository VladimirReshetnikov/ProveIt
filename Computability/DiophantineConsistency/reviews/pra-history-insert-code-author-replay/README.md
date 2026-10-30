# Candidate-PRA insertion-code replay

`PRA_has_insertCode` proves that a primitive-recursive code obtained from the bounded characteristic compiler satisfies the actual Foundation `insertDef` in candidate PRA. The constructor uses the verified exponential code. This is a component of the sequence constructor; no history, refutation witness, or HA-equivalence proof follows here.

The author and two independent peers passed and matched every source, object, and log hash. The replay authenticates 81 reachable project parent source/object pairs and direct Foundation IOpen/Basic, Exponential/Exp and Exponential/Bit anchors. The parent is an overlay of two independently passed peers; their state hashes are checked. Other Foundation and package provenance is inherited.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-history-insert-code-author-replay/replay.py --parent /tmp/pra-history-insert-parent/lib
```
