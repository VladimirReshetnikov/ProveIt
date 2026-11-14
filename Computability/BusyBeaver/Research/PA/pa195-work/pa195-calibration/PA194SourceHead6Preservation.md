# Internal PA proves numerical head6 translations

`PA194SourceHead6Preservation.lean` proves model-uniform internal PA
provability of the positive arithmetic translation of every numerical head6
instance, the source universal-distribution axiom

```
(U label a) → (U label (a → h)) → (U label h).
```

The label and both source codes may be arbitrary, including nonstandard,
model values. For a nonzero inner implication, the proof uses the internal
formula-closing traversal's compatibility with implication and constructs the
corresponding quantified distributivity derivation in Foundation's PA
calculus. If the inner implication is the alias `I(0,0)=0`, it instead uses
internal implication reflexivity and consequence introduction.

The theorem holds in every nonempty candidate-PRA model with equality and an
IΣ₁ arithmetic reduct. Its printed dependencies are `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`. This proves one
concrete source seed family; it does not by itself establish preservation of
the other source axioms, an actual machine-trace bridge, an object-theory
iPRA theorem, or the PA194 consistency equivalence.

Run `check-source-head6-preservation.sh` with the audited `IPRA_LEAN_OVERLAY`
and `IPRA_FOUNDATION_OVERLAY` set; it rebuilds the dependencies in a fresh
temporary overlay and rejects `sorryAx`.

The author completed a full fresh replay with no `sorryAx`. An independent
suffix replay also recompiled the final theorem against retained prerequisite
overlays; that suffix replay did not rebuild the dependency chain.
