# Arity-zero semiformula sigma conditional bound

`PRASemiFormulaSigmaBound` proves that Foundation's exact `isSemiformula L` sigma graph at arity zero has a bounded translation at `w` when `0<w`, its inlined `isUFormula L` sigma graph is bounded at `w`, and its inlined `bvGraph L` at value zero is bounded at `w`. The bounded-variable witness is zero; candidate PRA proves the corresponding universally closed conditional sentence.

Both syntax-graph bounds remain explicit and are not supplied here. The complete formula-set bound, derivation rule tail, recursive history, refutation certificate and HA equivalence remain open. The replay authenticates the current local parent graph, the direct formula-set dependency and selected Foundation source/object anchors; other Foundation and Mathlib transitive dependencies are inherited.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-semiformula-sigma-bound-author-replay/replay.py --parent /tmp/pra-formulaset-witness-bound-465hyx8m/lib --expected Computability/DiophantineConsistency/reviews/pra-semiformula-sigma-bound-author-replay/author/state.json
```
