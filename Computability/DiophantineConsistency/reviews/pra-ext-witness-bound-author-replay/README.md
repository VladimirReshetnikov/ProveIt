# Foundation extDef local witness bound

`PRAExtWitnessBound` proves that, in every model of IOpen, Foundation's exact `extDef` graph on arguments `(a,b,c)` entails its `bnd` translation at `c+1`. Its two bounded existential witnesses are at most `c`: the first is bounded by `c`, and the nested remainder witness is bounded by the first. The file maps the result to arbitrary candidate-PRA models and derives the universally closed sentence in candidate PRA by model completeness.

Foundation uses `extDef` inside `exponentialDef`. This theorem does not yet bind its substituted occurrences or bound `Seqₛ`, `ppow2Def`, `exponentialDef`, `bitDef`, the fixpoint, or ρ. In particular, it is not a proof of the desired HA equivalence.

The replay authenticates the 35-module inherited local graph, the direct `PRALenbitWitnessBound` source and object, and selected Foundation source/object pairs including `Exponential/Exp`. The rest of the Foundation and Mathlib transitive package graph is inherited from the parent provider; the replay is not a source rebuild of those packages. The parent provider `/tmp/pra-lenbit-bound-9nnf4u_8/lib` has a terminal PASS state and was independently replayed.

Run from the repository root:

```sh
python3 Computability/DiophantineConsistency/reviews/pra-ext-witness-bound-author-replay/replay.py --parent /tmp/pra-lenbit-bound-9nnf4u_8/lib --expected Computability/DiophantineConsistency/reviews/pra-ext-witness-bound-author-replay/author/state.json
```
