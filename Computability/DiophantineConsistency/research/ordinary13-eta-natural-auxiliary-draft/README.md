# Eta-natural auxiliary geometry and offset: source-only drafts

This packet contains two **unelaborated** source drafts. Neither derives its
premises from a graph zero, proves a graph zero map, or claims an equation
reduction. The `.lean.src` files are inert; no Lean build or provider check has
been performed.

`AuxGeometryEtaNatural.lean.src` is generated from the pinned
`research/ordinary14-aux-geometry-model-draft/AuxGeometry.lean`. Its only
mathematical change is to drop the premise `0 < eta`, retaining `eta : V` as
a model natural. Given `Y>0`, `k≥8*X*Y*Y+4`, and
`(X*Y+Y+2)²=Delta+1`, it proposes the original conclusion

```
A = X*Y+Y+2, c = eta+Y*k
A<c, 1<c, 0<Delta, Delta<c³.
```

The proof's penultimate inequality `A<Y*k` was already strict. Therefore
`Y*k≤eta+Y*k` is sufficient even at `eta=0`. Its proof body, imported theory,
and `IΣ₁` model parameters otherwise follow the pinned original source; the
exact text transformation and source hash are checked by the generator.

`AuxOffsetFacts.lean.src` is a separate fact-level client in the ordered
difference ring. It proposes two interfaces:

1. From `c>1`, `i≥1`, `0<Delta<c³`, the strong norm
   `(i*c²)²+Delta=Delta*f²`, the exact signed multiple
   `z+c=f²*t`, and `Q=(i*c²)²`, derive `Q>1` and `z²>1`. This composes the
   pinned `strong_f_square_large`, `strong_Q_gt_one`, and
   `signed_square_gt_one` source drafts; it does **not** assume `z²>1`.
2. From `Q>1`, `z²>1`, and `directAux z Q (ι y)=0` with **model-natural**
   `y`, derive a strictly positive model-natural `u` with `z+ιu=ιy`.
   It first uses the auxiliary norm to get `z²<(ιy)²`. Since `ιy≥0`, this
   forces `ιy>0`, then `z<ιy` and a positive represented difference. It does
   **not** assume `y>0` or `u>0`.

The client's imports `AuxRootBounds` and `AuxRootBridge` are proposed module
names for the separately pinned research draft sources, **not** existing built
providers. In particular, `AuxRootBridge` itself imports a further research
provider (`FirstRootBridge`); a real overlay must resolve and check that
closure. The geometry module is not automatically connected to the signed
facts: transporting its natural inequalities through `ι`, identifying
`Delta`, and matching the strong norm and signed multiple to the exact graph
remain explicit obligations. The large-`k` premise is also not discharged;
the original `first_ordinate_large` draft requires its own first norm and
`k>2`. None of this packet establishes those premises or the corresponding
internal iPRA proof.

From this directory, reproduce the byte and interface receipts with

```
python3 -I -S -B generate_geometry.py > /tmp/eta-natural-geometry.json
cmp geometry-result.json /tmp/eta-natural-geometry.json
python3 -I -S -B check.py > /tmp/eta-natural-aux-facts.json
cmp facts-result.json /tmp/eta-natural-aux-facts.json
```

The generator's optional `--write` regenerates the geometry copy. The second
checker pins the cited source files and records the fact-client hash. Both
checks are lexical, not Lean or mathematical proof verification.
