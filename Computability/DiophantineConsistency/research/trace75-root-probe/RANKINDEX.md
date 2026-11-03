# Trace75 rank and the auxiliary index

`Trace75RankIndex.graph_rank_auxiliary` is Lean checked in every `IΣ₁` model.
For arbitrary natural ports with model inequalities `31≤beta`, `MC<beta`,
`MF<2*beta`, and a positive trace75 ring zero, it returns one coherent tuple
`I,j,h` with positive I,j, `c²∣I`, the strong Pell x/y coordinates, and both
signed residues

```
SignMod F c (ycoord (2*h+1) (A-1)),
SignMod c rankNat (2*h+1).
```

Here `A=X*Y+Y` and `F=1+2*Delta*U²*E`. Its proof uses the V-square from the
same exported joined-square tuple, and proves `F % c = 1 % c` directly from
`U=i*c²`; it does not substitute the 80 chart's squared multiplier or combine
independently chosen V0 witnesses. K0 is arbitrary. No equality of rank with
the main index, halt/iPRA, trace74 reverse guard or external file binding is
claimed.

Accepted source `Trace75RankIndex.lean` SHA-256
`1532fc93288929e13209bc97d4bc4d3946e5cbdfea91d649d2716d4c91011f28`;
`run-rankindex-v2.py` accepted `observations/rankindex-attempt02/`, object
`/tmp/trace75-rankindex-g00v7ao8/Trace75RankIndex.olean` SHA-256
`9eeb3bbba40a1cb450220a8b64592c5ece3838d3f6093f6955d8c3e3f79cf248`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`. The first
failed attempt and its snapshot are retained; it exposed the missing V-square
export and is not part of the accepted chain. Selected direct/nearby inputs
are pinned; project/package transitive, historical source/object,
between-stage and dynamic ancestry remain inherited.
