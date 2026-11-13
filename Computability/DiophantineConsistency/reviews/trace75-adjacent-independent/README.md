# Independent review: trace75 adjacent quotient

The frozen accepted source supports the stated necessary condition for a positive trace75 zero. `check.py` rehashes its source/copies, runner, Lean binary, recorded pinned inputs, object and logs, and resolves direct and selected support objects through the recorded search path. The exact selections are in `check-output.txt`. We did not replay Lean or audit complete transitive/package/dynamic producer ancestry.

In an `ORingStructure V` model of IΣ₁, `Trace75Adjacent.graph_adjacent` takes arbitrary natural ports `p` with `0 < (p 0 : V)`, a single all-positive tuple `v`, and zero of the Lean `value75` at the same port casts and embedded coordinates in `DiffRing V`. It uses the actual `Trace75Factors` model expressions `D=delta p v`, `U0=U p v`, `E0=E p v`, `M0=M p v`, `a=D*U0*U0*E0`, and `Q=D*(4*a*(1+a))`.

The conclusion is one existential tuple `tau,f,V0,Z0,y` in `V`, with `tau`, `f`, `V0`, and `y` strictly positive; `Z0` is natural-valued but is not separately required positive. The same tuple satisfies `E0=tau²`, `1+a=f²`, the signed graph registers' square equalities `Vreg²=ι(V0²)` and `Zreg²=ι(Z0²)`, and

```
Z0 = (M0*tau*f)*y
Q*V0² = 1 + (Q−1)*y².
```

The source proves `1<Q` before using the model's truncated `Q−1`; it also proves `0<Q*V0²` before casting its subtraction of one into the difference ring. The resulting ring equation is rearranged and injected back to the model, then `S=M0*tau*f` and `B=Q−1` satisfy the scaled norm required by `TenPositiveAdjacentInteger.quotient_of_scaled_norm`. That direct provider returns the *same* quotient `y` for both equations; the source proves `y>0` using `Q>1` and `V0>0`. This is a necessary condition, not a converse, trace74 guard, halt equivalence, iPRA proof or formal binding of the external JSON/coefficient files.

The accepted object is `f8b22b6107778dd98a51e6aa356d8190a0be377c811bceeff43dfcd1b19f17ea` and its two direct imports first resolve to the audited `Trace75Factors` object `1bae9331cfbca4e35cb48916f135b63eedc8b5c827f8f24ae6f12b2dff111975` and `AdjacentInteger` object `19321c96c92462072fc3fe6cf30212535baa29e7915e1e59ca2c26073873dc34`. All selected adjacent descent providers, root/factor objects, and model/trace overlay selections match recorded pins. Their exact first paths are checked post hoc; pinning those objects does not establish their complete compile-time transitive provenance.

The accepted receipt records inner Lean exit 0, and the sole log report is exactly `[propext, Classical.choice, Quot.sound]`, with empty stderr. The runner rejects coded warning/error diagnostics and `sorryAx`, but does not enforce a named axiom whitelist; the report was independently checked. The terminal is emitted before the runner's final acceptance guard, and no separately retained actual outer-exit receipt was found.
