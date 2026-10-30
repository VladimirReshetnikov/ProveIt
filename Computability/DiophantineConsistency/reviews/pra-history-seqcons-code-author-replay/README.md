# Candidate-PRA seqCons-code replay

Candidate PRA proves that a primitive-recursive composition of the extracted length and insertion codes and explicit pairing code satisfies the exact Foundation `seqConsDef` graph. This does not prove any recursive history invariant, refutation bound, or HA equivalence.

The author and two independent peers passed and matched every source, object, and log hash. The replay authenticates 83 reachable project parent source/object pairs, direct Foundation IOpen/Basic, HFS/Seq, Exponential/Bit and Exponential/Exp anchors, and recursively checks the constituent overlay state hashes. Other Foundation and package provenance is inherited.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-history-seqcons-code-author-replay/replay.py --parent /tmp/pra-history-seqcons-parent/lib
```
