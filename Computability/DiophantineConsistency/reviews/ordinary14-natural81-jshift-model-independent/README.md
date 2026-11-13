# Independent source review: natural-81 J-shift model draft

The [draft](../../research/ordinary14-natural81-jshift-model-draft/README.md) proposes the mathematically correct changed-valuation relation from the natural-81 graph to the natural-82 graph. Its zero-to-predecessor argument explicitly assumes that port 1 is represented by a strictly positive model element `κ`. The source has not been elaborated, so this review does not establish a Lean model theorem or an iPRA derivation.

The independent receipt checks both Lean graph blocks against their pinned JSON graphs and compares all rows: the 82 graph's sole extra node is `J=n_J+1`, and each consumer in the 81 graph uses `n_J`. Therefore, over any commutative ring, the 81 output at `v81` agrees with the 82 output at `v82` when `v82[0]=v81[0]-1` and other coordinates agree. For natural-model witnesses, the draft correctly reverses this to `v81[0]=v82[0]+1`. Incrementing the 82 coordinate maps a zero to the 81 graph; the reverse direction needs a predecessor.

At a hypothetical 81 zero with `J=0`, the pinned graph's guard is exactly `−(n_F+n_alpha+1)*(n_w+1+κ)−n_F` in the difference ring. The receipt checks the relevant gate rows and this ring identity as a sparse formal polynomial, independently of numerical samples. Model elements embed as nonnegative values; strict `κ>0` and discreteness give `κ>=1`, so the guard is at most `−2`. The graph output is a product of four other factors and this guard minus one. If that product were one, its remaining factor would have to be negative; discreteness then makes its negation at least one, so the product would be at least two, a contradiction. No exclusion of `−1` for the other factors or positivity of beta is required for this local argument. Natural-model order and additive-predecessor facts are then needed to produce the witness.

The source uses the cited `ModelDifferenceRing` embedding/order statements and states both `(p 1 : DiffRing V)=ι κ` and `0<κ` explicitly. The intended selected symbolic port must still supply those hypotheses. The proposed `simp`, `ring`, `nlinarith`, instance search, model conversions and predecessor rewrite have not been checked by Lean; their resource and axiom behavior are unknown. Neither this review nor the draft binds physical coefficients or the displayed PDF.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural81-jshift-model-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural81-jshift-model-independent/result.json
```
