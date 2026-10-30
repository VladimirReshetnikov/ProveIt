# Negative pow2 witness bound

`PRANegPow2WitnessBound` proves that the negation of Foundation's exact `pow2Def` graph at `a` implies its bounded translation at `a+1`, in every IOpen model. It derives the corresponding universally closed candidate-PRA sentence using model completeness. The proof bounds the counterexample and divisor witness by `a`; the negated bounded divisibility condition requires no unbounded collection.

The result handles the local polarity that appears when `pow2Def` occurs in an antecedent. It does not yet bind that occurrence inside `sppow2Def` or prove bounds for `ppow2Def`, `exponentialDef`, `bitDef`, the fixpoint, or ρ. The HA equivalence is still open.

The replay authenticates the post-three-induction 34-module rebuild, 195 inherited local parent source/object pairs, and selected Foundation source/object anchors including `PPow2` and `Pow2`. Other Foundation and Mathlib transitive dependencies are inherited rather than rebuilt.

After freezing the author receipt, run:

```sh
python3 Computability/DiophantineConsistency/reviews/pra-negpow2-bound-author-replay/replay.py --parent /tmp/pra-after-three-induction-refresh-hzfafndb/lib --expected Computability/DiophantineConsistency/reviews/pra-negpow2-bound-author-replay/author/state.json
```
