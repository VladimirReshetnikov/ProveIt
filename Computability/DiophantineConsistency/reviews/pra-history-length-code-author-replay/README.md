# Candidate-PRA length-code replay

Candidate PRA proves that the actual Foundation `lhDef` has an output bounded by `2*s`, and has a primitive-recursive code for this output. The construction analyzes the actual `seqDef` syntax and applies bounded-witness extraction. No IΣ₁ induction or sequence-history existence is assumed.

The author and two independent peers passed and matched every source, object, and log hash. The replay authenticates 78 reachable project parent source/object pairs and the direct Foundation IOpen/Basic and HFS/Seq source/object anchors. Other Foundation and package provenance is inherited.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-history-length-code-author-replay/replay.py --parent /tmp/pra-cseq-witness-bound-independent-exj6vncw/lib
```
