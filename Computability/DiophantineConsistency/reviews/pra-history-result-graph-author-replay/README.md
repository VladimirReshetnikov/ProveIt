# Candidate-PRA Foundation recursion result graph

Given candidate-PRA proofs of the actual zero and step graphs for an arity-zero `PR.Blueprint`, candidate PRA proves the exact Foundation `resultDef` graph for the corresponding primitive-recursive iterator. The proof constructs the actual `cseqDef` history witness from the verified sequence trace. The zero and step graph certificates are explicit premises; the concrete ZFC derivation core and HA equivalence remain open.

The author and two independent peers passed and matched all source, object, and log hashes. The replay authenticates 96 reachable local source/object pairs and direct Foundation IOpen/Basic, HFS/Seq and HFS/PRF anchors; remaining Foundation/package provenance is inherited. An initial author attempt failed before compilation because of an incorrect parent path and is preserved in `failed-author-state.json`.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-history-result-graph-author-replay/replay.py --parent /tmp/pra-cseq-witness-bound-independent-s6n4hi10/lib
```
