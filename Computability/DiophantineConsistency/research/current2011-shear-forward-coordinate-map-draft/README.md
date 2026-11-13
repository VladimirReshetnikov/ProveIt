# Proposed forward coordinate-12 witness map

This **unelaborated source-only draft** proposes the entire forward model
map from the current2011 positive-shifted 71/60 zero to a positive-shifted
72/46 zero. It composes several other uncompiled local drafts, so it is not
a checked theorem, an established zero map, or an iPRA endpoint. No Lean or
build is run here.

Let `u j = ι(v j+1)` be the parent valuation in the model difference ring,
and let `V=(Carrier65.core currentP u).V`. The proposed component lemmas
use the actual parent zero to derive `V<u 12` from the signed rank bound
and the ordinary sphere's auxiliary unit norm. The separate positive-gap
representation draft proposes a natural n satisfying

```
ι(n+1) = u 12 − V.
```

The new natural child valuation is `Function.update v 12 n`; every other
coordinate is unchanged, and its **positive-shifted** coordinate 12 embeds
as `ι(n+1)`. The source draft explicitly proposes the complete valuation
identity

```
shiftedRing (Function.update v 12 n)
  = Function.update (shiftedRing v) 12 (ι(n+1)).
```

The core carrier V does not use coordinate 12. Therefore the existing
proposed all-ring shear from the 72/46 literal-evaluator draft maps the
updated child ring valuation back to **every coordinate** of u. The draft
then transports the parent ring zero through the shear and back through
`internalZero_iff` and `internalZero_positiveShift`.

[`ForwardCoordinateMap.lean.src`](ForwardCoordinateMap.lean.src) keeps a
separate `forward_zero_of_rep` theorem with the representative equality
explicit, then proposes `forward_zero` by applying the positive-gap,
rank-cast and norm-order drafts. The finite-index `Function.update` simp,
literal evaluator, `InternalZero` conversions, imported names and all
provider choices remain untested. The concrete current ports include the
high-mask beta shift once through the pinned parent ports.

The separately drafted reverse magnitude/witness route, compilation and
independent validation of both directions, final no-zero equivalence,
and encoded iPRA/Gödel–Gentzen clients all remain required. The physical
PDF/TeX semantics and transitive provider limits remain as documented in
the earlier endpoints.

The read-only [checker](check.py) pins the six direct draft sources and
checks selected theorem markers and explicit coordinate-12/successor
structure. It does not parse Lean, establish its typechecking, run proofs,
or authenticate transitive imports.

```
python3 -I -S -B research/current2011-shear-forward-coordinate-map-draft/check.py > /tmp/shear-forward-map.json
cmp /tmp/shear-forward-map.json research/current2011-shear-forward-coordinate-map-draft/result.json
```
