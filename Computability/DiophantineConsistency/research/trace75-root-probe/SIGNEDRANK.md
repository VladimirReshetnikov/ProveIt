# Single-multiplier signed rank residue

`Trace75SignedRank.rank_residue_of_square` is a generic Lean theorem in every
`IΣ₁` model. For positive modulus c and model elements f,t,rp,rn,u with
`f % c = 1 % c`, and a difference-ring value

```
x = ι(f)*(ι(t*c)+ι(rn)-ι(rp)) - ι(c),
x² = ι(u²),
```

it derives `SignMod c u (absdiff rp rn)`. It preserves both signs of the
represented rank and uses a **single** f multiplier, matching the trace75
unsquared V register. It is generic; it does not bind f or the rank to an
actual graph, identify any Pell index, prove halting, an iPRA theorem, or a
trace74 guard.

Accepted source `Trace75SignedRank.lean` SHA-256
`7e825700c5196ad265a5c29635f6667222c913b927d086c413e72bbba25d1949`;
`run-signedrank.py` accepted `observations/signedrank-attempt01/`, object
`/tmp/trace75-signedrank-wtu23ycl/Trace75SignedRank.olean` SHA-256
`7b0050d97800e27c67bed2912b68c5653861c8af2527c911701721bdcfbebe51`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`. Selected
direct imports and nearby support are pinned; project/package transitive,
historical source/object and dynamic ancestry remain inherited.
