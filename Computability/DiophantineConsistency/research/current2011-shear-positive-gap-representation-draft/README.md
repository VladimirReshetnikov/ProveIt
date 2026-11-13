# Positive difference-ring gap as a shifted natural coordinate

This inert Lean source proposes a generic IΣ₁-model lemma, independent of the 72/46 graph: if `0 < D : DiffRing V`, then `∃ n : V, ι (n+1) = D`. `ModelDifferenceRing.nonneg_iff` supplies a model-natural a with `D=ι a`; positivity rules out a=0, and model discreteness permits `n=a−1`, with `n+1=a`. The derived `positive_gap_as_successor` takes `signedV < yParent` and returns a representative for `yParent−signedV`. This has the orientation needed by a forward positive-shifted coordinate, rather than the reverse absolute-value square witness.

The source is not elaborated. In particular the `nonneg_iff` instance, simp at model zero, truncated-subtraction cancellation, casts, tactic elaboration and providers remain to be checked. The theorem takes strict positivity as a premise; it does not establish that premise at a 71/60 graph zero, bind any literal graph, or prove a two-way zero map or iPRA theorem. The `#print axioms` commands are not reports. No Lean/build/staging was performed.

The checker pins this source and the declared difference-ring interface, checks exact theorem shapes, and exercises bounded standard integer controls. Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/current2011-shear-positive-gap-representation-draft/check.py | cmp - research/current2011-shear-positive-gap-representation-draft/receipt.json
```
