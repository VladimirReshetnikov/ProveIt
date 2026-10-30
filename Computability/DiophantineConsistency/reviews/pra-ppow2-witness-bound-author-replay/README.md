# Foundation ppow2Def graph bound

`PRAPpow2WitnessBound` proves that Foundation's exact positive `ppow2Def` graph at `i` entails its bounded translation at `2*i+1` in every IOpen model. It binds the full `sppow2Def`, positive `pow2Def`, and lenbit bounds into the actual bounded existential, with no bounded collection or IΣ₁ assumption. Candidate PRA proves the universally closed bound sentence.

The proof handles the positive graph only. Negative `ppow2Def`, the full exponential graph, bit membership, the fixpoint, ρ, and the target HA equivalence remain open.

The replay authenticates the source-current local parent graph, selected Foundation source/object anchors, and its parent terminal state. The remaining Foundation and Mathlib transitive dependencies are inherited rather than rebuilt from source.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-ppow2-witness-bound-author-replay/replay.py --parent /tmp/pra-after-sppow2-merge-independent-ite3o4qo/lib --expected Computability/DiophantineConsistency/reviews/pra-ppow2-witness-bound-author-replay/author/state.json
```
