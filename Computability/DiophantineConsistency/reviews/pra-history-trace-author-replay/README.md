# Candidate-PRA actual sequence history trace

For arbitrary supplied primitive-recursive base and step codes, candidate PRA has a code for a valid actual sequence trace of length `n+1` containing every `(i,valueCode(i))` entry for `i<n+1`. The proof builds the history by primitive recursion and uses bounded-characteristic quantifier-free induction; the certified actual sequence-cons code is supplied internally. The bridge to a particular Foundation `cseqDef` and its concrete blueprint certificates remain separate.

The author and two independent peers passed and matched all source, object, and log hashes. The three-parent overlay constituent states, 95 reachable project source/object pairs and listed direct Foundation anchors are authenticated; remaining Foundation/package provenance is inherited.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-history-trace-author-replay/replay.py --parent /tmp/pra-history-trace-parent/lib
```
