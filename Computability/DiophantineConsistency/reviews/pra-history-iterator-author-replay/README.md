# Candidate-PRA history iterator replay

This is an explicit primitive-recursive iterator whose base and successor equations hold in every candidate-PRA model for supplied base, step and cons codes. It does not assert the actual `cseqDef` invariant or construct the concrete blueprint step code.

The author and two independent peers passed and matched every source, object, and log hash. The replay authenticates 84 reachable project source/object pairs and direct Foundation IOpen/Basic and HFS/Seq anchors. Other Foundation and package provenance is inherited.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-history-iterator-author-replay/replay.py --parent /tmp/pra-cseq-witness-bound-independent-fjq8y6jr/lib
```
