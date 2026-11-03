# Trace75 odd main index at least five

`Trace75MainFive.graph_main_index_ge_five` is Lean checked in every `IΣ₁`
model. At arbitrary natural ports satisfying `2≤beta` in the model, for ten
positive witnesses at which the Lean trace75 ring value is zero, it produces
one tuple of model witnesses `r,j,I` with

```
5 ≤ r < j,  r % 2 = 1,  0 < j,  0 < I,
c = ycoord r (A-1),  2*r < c,
xcoord j (A-1) = 1 + 2*Delta*U²*E,
ycoord j (A-1) = I,  c² ∣ I.
```

The local natural `A` is `X*Y+Y`. The first-index witness used to exclude
`r=3` comes from the same graph valuation; it is not exported in this theorem.
The proof excludes `r=4` by oddness and uses the separately checked
`Trace75ThreeExcluded` for `r=3`. The beta bound is a hypothesis, not a
fixed-port specialization. This is a necessary consequence of a trace75 zero,
not a converse, halt equivalence, trace74 guard, iPRA theorem, or formal
JSON/payload binding.

Accepted source `Trace75MainFive.lean` SHA-256
`ff17df73722cb9dd0fdd1b1f3693e6e570259f6b7c777edd8f3968309c5910cd`;
`run-mainfive-v3.py` accepted `observations/mainfive-attempt03/`, object
`/tmp/trace75-mainfive-ita7pfhk/Trace75MainFive.olean` SHA-256
`8888ae54e909078ce31cfc1fae7857295827fd7d0e8bc609e4dbaffefd1c95f1`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
Both earlier failed attempts, source snapshots and logs are retained. Direct
providers and nearby dependencies are pinned. Project/package transitive,
historical source/object and dynamic ancestry remain inherited; no full
selected closure audit or independent Lean replay is claimed.
