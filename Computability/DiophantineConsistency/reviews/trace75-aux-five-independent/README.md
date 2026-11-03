# Independent review: trace75 auxiliary index at least five

For any `ORingStructure V` model of IΣ₁, the accepted `Trace75AuxFive.graph_auxiliary_index_ge_five` assumes arbitrary natural ports `p` with explicit model bound `2≤(p 0 : V)`, an all-positive tuple `v : Fin 10 → V`, and zero of Lean's trace75 `value75` at the same ports and embedded coordinates in `DiffRing V`. It returns **one** tuple `I,j,h : V` with `0<I`, `0<j`, `2≤h`, `c≤I`, `c²∣I`, the strong `xcoord j` and `ycoord j=I` equations at the chart `A−1`, and

```
SignMod (1+2*delta*U²*E) c (ycoord (2*h+1) (A−1)).
```

Thus its indicated odd auxiliary index `2*h+1` is at least five. `SignMod` is the imported signed congruence, not direct equality. All expressions are those of the same `p,v`; the theorem does not identify the auxiliary index with a main or first index.

The proof obtains `I,j,h` from `Trace75Fold.signed_coordinate`. Separately, it uses `Trace75MainSize.graph_main_size` on the same `p,v` to obtain the coordinate-independent bound `4*delta+3<c`; its existential witnesses `r,j0,I0` are **not** identified with the returned `j,I`. Positivity, `c²∣I` and the strong Pell norm give the internal size estimate `2*c<F`. Under signed congruence this excludes `h=0` using the first ordinate and `h=1` using `ycoord 3 (A−1)=4*delta+3` and the strict main-size bound. The conclusion directly exports `h≥2`, not an explicit `2*c<F` or `4*delta+3<c` conjunct. This is a necessary condition for a positive Lean trace75 zero, not index alignment, a trace74 guard, halt/iPRA equivalence or Lean binding of external JSON/coefficient bytes.

`check.py` rehashes source/copies, runner, Lean binary, recorded inputs, object and logs; checks first resolution of the direct and selected inherited providers; and checks the earlier failed attempt. The sole direct provider is reviewed `Trace75MainSize` `617754ec439b63ae5ab242ce2c161d0b500b3925220b1a790ac6f6c151d6555f`. The inherited `ArithmeticPellFirstNorm` is not separately pinned by this runner; its post-hoc first hash matches the earlier accepted `Trace75Pell` producer's direct pin. Exact paths/hashes are in `check-output.txt`; this does not establish a complete transitive/project/package/dynamic producer history.

Accepted attempt02 has output `4cedad6c7e803f3d9c262f2b90910fb8988850075b628708e9468c84d8d15381`, inner exit 0, empty stderr and the sole named axiom report exactly `[propext, Classical.choice, Quot.sound]`. Attempt01 had nonzero Lean exit and is not accepted. The runner rejects coded warnings/errors and `sorryAx` but does not enforce a named axiom whitelist; the report was independently inspected. Its terminal precedes final assertions and no separately retained actual outer-exit receipt was found. No Lean replay was performed.
