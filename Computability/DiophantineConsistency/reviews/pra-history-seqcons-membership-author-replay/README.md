# Candidate-PRA sequence-append membership replay

Candidate PRA proves that an actual `seqConsDef` result has a bounded `lhDef` value and contains exactly its prior `memRel` entries plus the new length/value pair. The model bridge obtains IΣ₀ from candidate PRA and exponential witnesses from the verified code. No IΣ₁ hypothesis is used; sequence validity, length evolution, and the full history invariant remain open.

The author and two independent peers passed and matched every source, object, and log hash. The replay authenticates 85 reachable project source/object pairs and direct Foundation IOpen/Basic, HFS/Seq, Exponential/Pow2, Exp and Bit anchors. Other Foundation and package provenance is inherited.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-history-seqcons-membership-author-replay/replay.py --parent /tmp/pra-cseq-witness-bound-independent-c9npnuwa/lib
```
