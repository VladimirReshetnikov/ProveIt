# Rewritten extDef local bound

`ext_rew_bound` transfers the exact Foundation `extDef` local majorant through any arithmetic rewriting in an IOpen model: the value of its third rewritten argument plus one bounds all of its existential witnesses. `initialX_bound` applies it to the specific expression `“X. !extDef 1 4 X”`, which appears in Foundation's `exponentialDef`, and `candidate_proves_initialX_bound` is a candidate-PRA derivation of its universally closed bound sentence.

This proves neither the binding of that occurrence into the whole exponential formula nor a bound for its other conjuncts. In particular `Seqₛ`, `ppow2Def`, `exponentialDef`, `bitDef`, the fixpoint and ρ remain open, as does the intended HA equivalence.

The replay authenticates the inherited local parent graph, direct local `PRAExtWitnessBound` and `PRALenbitWitnessBound` source/object pairs, and selected Foundation source/object pairs including `Exponential/Exp`. It separately authenticates the state, source, and object of the independently replayed `PRABndRewriting` provider. The remaining Foundation and Mathlib transitive package graph is inherited, not rebuilt from source.

Run from the repository root:

```sh
python3 Computability/DiophantineConsistency/reviews/pra-ext-rewriting-bound-author-replay/replay.py --parent /tmp/pra-ext-bound-asis2thv/lib --expected Computability/DiophantineConsistency/reviews/pra-ext-rewriting-bound-author-replay/author/state.json
```
