# Negative Foundation sppow2Def graph bound

`PRANegSppow2WitnessBound` proves that the negation of Foundation's exact `sppow2Def` graph at `m` entails its bounded translation at `m+1` in every IOpen model, and derives the universally closed candidate-PRA sentence. The proof bounds both branches of the negated iff using the positive and negative sqrt/lenbit and pow2 bounds, without bounded collection or IΣ₁.

Negative `ppow2Def`, the full exponential graph, bit membership, the fixpoint, ρ, and the HA equivalence remain open.

The replay authenticates the source-current local parent graph, selected Foundation source/object anchors, and its parent terminal state. The other Foundation and Mathlib transitive dependencies are inherited rather than rebuilt from source.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-negsppow2-witness-bound-author-replay/replay.py --parent /tmp/pra-after-sppow2-merge-independent-ite3o4qo/lib --expected Computability/DiophantineConsistency/reviews/pra-negsppow2-witness-bound-author-replay/author/state.json
```
