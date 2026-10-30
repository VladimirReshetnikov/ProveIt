# Actual candidate-PRA proof of the first-index family bound

New sources: `PRAFstIdxFamilySentence.lean` and `PRAFstIdxFamilySentenceChecks.lean`. The two-module author run passed and authenticated 82 unchanged local source/object parents, using the root independently replayed `fstIdxDef` family provider. Private replay `/tmp/pra-fstidx-family-sentence-independent-fdxwlwus` and root replay `/tmp/pra-fstidx-family-sentence-independent-xcmjxzdd` passed with matching source, object and complete-log hashes. The author/root source snapshots, logs and all three terminal states are recorded; Foundation and Mathlib are inherited.

`candidate_proves_fstIdx_family` constructs an actual candidate-PRA proof of the universal sentence saying that, for every `x,p,k`, `p < k` and Foundation's mapped `fstIdxDef(x,p)` imply its exact syntactically bounded form with the common primitive-recursive fold of successor through `k`. The explicit substitutions and quantifier order are given by `familyBody` and `familySentence`. This establishes one local component; the remaining proof-predicate witnesses and the exact ZFC refutation bound certificate are not proved.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-fstidx-family-sentence-author-replay/replay.py \
  --parent /tmp/pra-fstidx-family-independent-rl6i2tv5/lib
```
