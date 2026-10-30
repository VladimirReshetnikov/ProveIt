# Derivation sigma-core outer binding

`PRADerivationCoreSigmaBound` checks the exact outer split of Foundation's `Derivation.blueprint T` sigma core and proves its first-index graph witness is at most `d` in every IOpen model. Given `d+1 ≤ w`, the original fst-index graph, the separately bounded formula-set graph, and the separately bounded entire ten-rule tail, it derives the bounded actual sigma core. Candidate PRA proves the corresponding universally closed conditional sentence.

The bounded formula-set graph and ten-rule tail are explicit premises and are not proved here. The negative pi core, recursive history, full refutation certificate, and HA equivalence remain open. The replay authenticates the source-current local parent graph, direct succ/negative-bit dependencies and selected Foundation source/object anchors; other Foundation/Mathlib transitive dependencies are inherited.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-derivation-core-sigma-bound-author-replay/replay.py --parent /tmp/pra-fixsucc-witness-bound-q94rldcu/lib --expected Computability/DiophantineConsistency/reviews/pra-derivation-core-sigma-bound-author-replay/author/state.json
```
