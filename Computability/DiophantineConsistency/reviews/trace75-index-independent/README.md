# Independent review: trace75 first index exclusion

The frozen accepted theorem gives a **universal bound on the supplied first index**. `check.py` rehashes source/copies, runner, recorded inputs, Lean binary, output and logs, and resolves direct and selected inherited objects through the recorded search path. `check-output.txt` records exact first paths and hashes. We did not replay Lean or audit complete transitive/package/dynamic ancestry.

For any `ORingStructure V` model of IΣ₁, `Trace75Index.first_index_ge_two` takes arbitrary natural ports `p`, any model tuple `v : Fin 10 → V` and **any** model `n`. It assumes `0<(p 0 : V)`, all coordinates of `v` positive, zero of the Lean trace75 `value75` at the embedded tuple and port casts in `DiffRing V`, and the explicit ordinate equation

```
2*ycoord n (2*(firstParam p v−1)+1) = k v,
firstParam p v = X p v*(Y p v*Y p v).
```

Under these assumptions it concludes `2≤n`. In particular the theorem does not merely bound a chosen witness from the first Pell classification: it bounds every `n` satisfying that equation. It does not assert that an arbitrary `n` satisfies it or that any zero exists.

The proof excludes `n=0` using positivity of `k=eta+zeta`. From the independently reviewed `Trace75Fold.graph_odd_ordinate` it obtains an actual main-chart ordinate witness `c=ycoord m (A−1)`. If `n=1`, the first-coordinate recurrence yields `k=2`; it invokes the generic `Direct80IndexOne.impossible` interval lemma with **unscaled** `S=Y`, `Y=Y p v`, and `A=Y*(X+1)`, together with the positive `eta,zeta`. That lemma is generic despite its module name and excludes this interval. This result does not prove a main-index bound, connect the two indices, or give a halt, iPRA, or external JSON/payload binding theorem. Its source-level proof requires no `Direct80Joined` or 80-graph-zero premise.

The three direct objects are the previously reviewed trace75 fold `60d26b62219b41539aecf950465beee7e90df5a50f78e14ac8670d47c2ef5263`, trace75 first Pell `cea9dcd9cc72467aa28113a65178cb7763170960ef0a4b215153537fb77bfbb9`, and generic index-one contradiction provider, all selected first and pinned. The inherited generic Pell chain first resolves to the freshly rebuilt generic root. `ArithmeticPellFirstNorm` is **not** a direct import or a separately pinned input of the index runner; its post-hoc first path is `/tmp/trace75-fold-b2hmelpc/DiophantineConsistency/ArithmeticPellFirstNorm.olean`, resolving to hash `82b45a6e4da9ab538940849ebb6515056e82a20fb7f57a353441a90f50438854`, which matches the direct pin in the earlier accepted `Trace75Pell` producer. That observation is not a compile-time transitive import snapshot.

The accepted output object is `6cc75eb28726516d4901542f26f083ecceeb682d459ff4a71022f3d88b1a3a34`; its inner Lean exit is 0, stderr empty, and its sole named report exactly `[propext, Classical.choice, Quot.sound]`. Attempt01 has nonzero Lean exit and is not the accepted artifact. The runner rejects coded warnings/errors and `sorryAx` but does not enforce a named axiom whitelist; the exact report was inspected independently. Its terminal precedes final assertions and no separately retained actual outer-exit receipt was found. Earlier generic rebuild and project/package transitive provenance boundaries remain inherited.
