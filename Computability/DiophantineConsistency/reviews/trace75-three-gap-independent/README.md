# Independent review: ordered-ring gap lemma

The accepted `Trace75ThreeGap.gap_bounds` is a generic theorem for every type with `[CommRing R] [LinearOrder R] [IsStrictOrderedRing R]`. It assumes arbitrary `x,y,eta : R` with `2≤x`, `8≤y`, `0<eta`, **strict** `eta<8*x*y²+4`, and the signed ring equality

```
eta + 4*y²*(x*(2*y−x−2)−1) = 4*y*(2*x+1)+3.
```

Its conclusion consists of **both strict inequalities** `x<2*y` and `2*y<x+3`. All operations and subtractions are in the ordered ring; the theorem is not restricted to integers and has no graph, natural-cast or IΣ₁-model hypotheses. The proof separately contradicts each possible closed complement using nonnegative products and ordered-ring arithmetic. The theorem does not establish that a trace75 zero supplies its bounds/equality and does not itself exclude the main-index-three case, prove a trace74 guard, halt equivalence or iPRA statement.

`check.py` rehashes source/copies, runner, Lean binary, all recorded pins, object and logs, and checks first resolution of all four direct Mathlib imports. Exact paths/hashes are in `check-output.txt`. Accepted attempt02 has object `3f25660d7a2263e82d60dbdea5815063a74bf29fcdabc3e8dc3c976f6d1a1850`, inner exit 0, empty stderr and sole named axiom report exactly `[propext, Classical.choice, Quot.sound]`. Attempt01 had nonzero Lean exit. The runner rejects coded warnings/errors and `sorryAx` but does not enforce a named axiom whitelist; this review checked the report separately. Its terminal precedes final assertions, and no separately retained actual outer-exit receipt was found. No Lean replay or complete package/dynamic producer audit was performed.
