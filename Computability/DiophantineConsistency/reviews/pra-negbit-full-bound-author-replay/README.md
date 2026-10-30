# Negative Foundation bit graph bound

`PRANegBitFullWitnessBound` proves the negation of Foundation's exact `bitDef` graph at `(x,y)` implies its bounded translation at `((2*y+1)+(2*y²+1))+y+1` in every IOpen model, and derives the corresponding closed candidate-PRA statement. It uses the negative exponential graph, monotonicity of its polynomial bound, and the negative lenbit graph without bounded collection or IΣ₁.

This supplies the membership polarity needed in the antecedent of `succDef`, but does not bound the other `succDef` core formulas, the recursive history, the full refutation certificate, or the HA equivalence. The replay authenticates the current local parent graph, the direct negative exponential dependency pairs, selected Foundation anchors, and parent terminal state. The negative exponential parent has two matching independent peer replays; other Foundation and Mathlib transitive dependencies are inherited.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-negbit-full-bound-author-replay/replay.py --parent /tmp/pra-negexponential-bound-662_anjz/lib --expected Computability/DiophantineConsistency/reviews/pra-negbit-full-bound-author-replay/author/state.json
```
