# Candidate-PRA fixpoint collector replay

An explicit PR collector starts at zero and adds each index selected by a supplied Boolean core code. In every candidate-PRA model it satisfies the complete bit-membership invariant: a bit is present iff its index is below the iteration bound and the core code selects it. The theorem explicitly assumes candidate-PRA proofs of Boolean range for the supplied core code, the actual insertion graph for the supplied insertion code, and correctness of a characteristic code for the actual bit graph.

It does not supply a characteristic code for the concrete derivation core, prove the full fixpoint successor graph, or establish a history, refutation bound, or HA equivalence. The author and two independent peers passed and matched every source, object, and log hash. The replay authenticates 85 reachable project source/object pairs and direct Foundation IOpen/Basic, Exponential/Pow2, Exp and Bit anchors. Other Foundation and package provenance is inherited.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-history-fixpoint-collector-author-replay/replay.py --parent /tmp/pra-cseq-witness-bound-independent-c9npnuwa/lib
```
