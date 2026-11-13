# Trace75 odd main index at least three

`Trace75MainIndex.graph_main_index` is checked in every `IΣ₁` model. For
arbitrary natural ports with beta positive and a positive valuation at which
the Lean trace75 ring value is zero, it strengthens the previously recovered
odd main ordinate: the same model witnesses `r,j,I` satisfy

```
3 ≤ r < j,   r % 2 = 1,   2*r < c,
c = ycoord r (A-1),
xcoord j (A-1) = 1 + 2*Delta*U²*E,
ycoord j (A-1) = I,   c² ∣ I.
```

The local `A` is `X*Y+Y`, so the Pell parameter is `A-1`. The proof excludes
r=1 using c>1 and r=2 using oddness, then applies the existing ordinate growth
bound. It does **not** exclude r=3, prove r≥5, align the main and first indices,
prove a halt equivalence or an iPRA theorem. External JSON/payload binding is
unchanged.

Accepted source `Trace75MainIndex.lean` SHA-256
`5691022bf0a09ace9d20699216856305861f23a850fa17ec9376a3ce802ece9b`;
`run-mainindex.py` accepted `observations/mainindex-attempt01/`, object
`/tmp/trace75-mainindex-6jrdblag/Trace75MainIndex.olean` SHA-256
`9296c438f1fc9dbaec85b2e67db0e3088b0b852072cc2867621cbcfb2f60b55c`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
Selected direct providers are pinned; project/package transitive, historical
source/object and dynamic ancestry remain inherited.
