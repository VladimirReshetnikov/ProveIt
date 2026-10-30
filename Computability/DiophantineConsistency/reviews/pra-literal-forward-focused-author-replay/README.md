# Literal current-equation forward implication: focused replay

The four-module author run `/tmp/pra-literal-forward-focused-mh6u9k6v`
passed. Root’s independent replay `/tmp/pra-literal-forward-focused-5aymngkm`
also passed, with all four source, object and full-log hashes matching the
author run. It constructs actual candidate-PRA proofs that the literal 14-variable
no-zero sentence is equivalent to `conB ρ`, and that the literal Foundation
ZFC consistency sentence implies that no-zero sentence. It does not prove the
reverse implication or establish either sentence separately. Both checks
report exactly `propext`, `Classical.choice` and `Quot.sound` as Lean axioms.

The replay authenticates the source/object pairs listed in the accepted
15-module generic-surrogate manifest and all 26 source/object pairs in the
independently replayed no-zero closure, before and after the four client
builds. It uses `/tmp/pra-strict-surrogate-postmerge-independent-vhkj_kj6/lib`
and `/tmp/pra-current-nozero-closure-samepath-independent-vpvwoq8y/lib`. The
prior `HACurrentEquation2011` IΣ₁ equivalence theorem and its transitive HA
and ZFC interpreter closure are inherited from a historical object provider;
the present run does **not** authenticate those sources or objects. Foundation,
Mathlib, PAHF, and the other unlisted transitive imports are also inherited.
Later upstream changes can make this a preceding-snapshot result.
The subsequent merge of `PRAOpenOneInduction` and `PRABoundedOneInduction`
changed the generic PRA provider's dependencies, so those affected inputs need
another refresh in addition to the historical endpoint closure.

`author/state.json` records the exact environment, hashes, build commands,
status and inherited endpoint hash. `author/logs/` contains the exact source
snapshots and complete compiler logs; `root-independent/` preserves the
corresponding root replay evidence. The original author object files remain
in its temporary provider. Run the independent replay with:

```sh
python Computability/DiophantineConsistency/reviews/pra-literal-forward-focused-author-replay/replay.py \
  --parent /tmp/pra-strict-surrogate-postmerge-independent-vhkj_kj6/lib \
  --closure /tmp/pra-current-nozero-closure-samepath-independent-vpvwoq8y/lib \
  --expected Computability/DiophantineConsistency/reviews/pra-literal-forward-focused-author-replay/author/state.json
```
