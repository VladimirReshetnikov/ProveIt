# Current graph after the exponential proof refactor

The author and two independent peers rebuilt 12 changed or new modules, including the refactored positive exponential proof and its exp/bit/conditional fixpoint descendants, plus the new negative `Exponential.Seqₛ.def` proof. The negative Seqₛ graph is bounded at `2*y+1` in arbitrary IOpen models and has a closed candidate-PRA derivation; it binds positive ppow2 and all eight negated ext substitutions. All source/object/full-log hashes match across the three replays.

The 18-module historical parent was independently replayed twice against a hash-verified frozen source snapshot. The source-current local dependency graph and selected Foundation source/object anchors are authenticated; the rest of the Foundation and Mathlib transitive graph is inherited. This does not yet prove the negative exponential, negative bit, full refutation, or HA equivalence results.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-after-exponential-refactor-refresh-author-replay/replay.py --parent /tmp/pra-after-late-bound-refresh-69zt8e1y/lib
```
