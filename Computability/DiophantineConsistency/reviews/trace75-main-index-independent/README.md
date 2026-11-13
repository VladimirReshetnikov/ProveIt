# Independent review: trace75 odd main index

The accepted `Trace75MainIndex.graph_main_index` is an IΣ₁-model theorem for arbitrary natural ports `p` with `0<(p 0 : V)`, one all-positive `v : Fin 10 → V`, and zero of the Lean trace75 `value75` at that same tuple and port casts in `DiffRing V`. It returns one `r,j,I` with `3≤r<j`, `r%2=1`, `0<j`, `0<I`,

```
c p v = ycoord r (A p v−1),    2*r < c p v,
xcoord j (A p v−1) = 1+2*(delta p v*U p v*U p v*E p v),
ycoord j (A p v−1) = I,       (c p v)² ∣ I.
```

The proof starts with the **same** recovered `r,j,I` from `Trace75Fold.graph_odd_ordinate`. Positive inputs imply `c>1`, which excludes `r=1` since the first ordinate is one; oddness then excludes `r=2`. The imported ordinate-growth bound gives `2*r<c` for the same `r`, with the chart explicitly `A−1` for `A=X*Y+Y`. The theorem does not exclude `r=3` or claim `r≥5`, align the main and first indices, establish machine halting or iPRA, or formalize external JSON/payload semantics.

`check.py` rehashes source/copies, runner, Lean binary, recorded inputs, object and logs, and resolves direct and selected inherited providers; paths and hashes are in `check-output.txt`. Its sole direct import is the independently reviewed `Trace75Fold` object `60d26b62219b41539aecf950465beee7e90df5a50f78e14ac8670d47c2ef5263`; selected generic Pell and trace75 support objects match recorded pins. These post-hoc selected objects do not constitute a complete historical/producer-time, project/package or dynamic closure audit.

The accepted object is `9296c438f1fc9dbaec85b2e67db0e3088b0b852072cc2867621cbcfb2f60b55c`; inner Lean exit is 0, stderr is empty and its sole named report is exactly `[propext, Classical.choice, Quot.sound]`. The runner rejects coded warnings/errors and `sorryAx` but does not enforce a named axiom whitelist; the report was independently inspected. The terminal precedes final runner assertions and no separately retained actual outer-exit receipt was found. No Lean replay was performed.
