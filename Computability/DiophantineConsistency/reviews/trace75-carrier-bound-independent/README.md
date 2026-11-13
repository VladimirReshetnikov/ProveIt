# Independent review: trace75 signed carrier magnitude bound

For any `ORingStructure V` model of IΣ₁, the accepted `Trace75CarrierBound.graph_carrier_bound` takes arbitrary natural ports `p` with **only positive beta** `0<(p 0 : V)`, an all-positive `v : Fin 10 → V`, and zero of Lean's trace75 `value75` at those same ports and embedded coordinates in `DiffRing V`. It concludes one coherent tuple `tau,f,V0,Z0,y : V` with `tau,f,V0,y` positive, signed actual graph-register square representatives `Vreg²=ι(V0²)` and `Zreg²=ι(Z0²)`, and

```
Z0 = (M p v * tau * f) * y,
2*(tau*f*y) < V0*V0.
```

`Z0` is natural-valued but has no explicit positivity conjunct. The proof obtains **that same tuple** from reviewed `Trace75Adjacent.graph_adjacent`; in particular its root and adjacent norm facts are used internally with the same `tau,f,V0,y`, though the root equalities are not restated in the carrier-bound conclusion. It applies reviewed `Trace75Residue.graph_signed_residue` to the actual signed `V` square representative for the same `V0`, using the **single unsquared** `F=1+2*delta*U²*E`. From positive beta and graph inputs it obtains the generic `CarrierSizes.sufficient` prerequisites, including `delta≥16`, and derives the size conditions for `Direct80CarrierEstimate.adjacent_carrier_bound`; that imported estimate is a generic arithmetic theorem despite its name.

This is a strict magnitude inequality, not a transport-sign theorem, a proof of natural nonnegativity of signed `B`, positivity of the old mask coordinate, an index-alignment result, a trace74 guard, halt/iPRA equivalence, or an internal binding to JSON/payload bytes. It assumes beta **positive**, not beta≥2.

`check.py` rehashes the source/copies, runner, Lean binary, recorded pins, object and logs; checks first-resolved direct and selected inherited providers. Direct imports select generic `Direct80CarrierEstimate`, `CarrierSizes`, and the independently reviewed `Trace75Adjacent` and `Trace75Residue` objects; exact paths/hashes are in `check-output.txt`. The output is `8ef47fc9a296744657c3f3dfd7130aeab24058371533a995a247e045318af923`, with inner exit 0, empty stderr and sole named report exactly `[propext, Classical.choice, Quot.sound]`. The runner rejects coded warnings/errors and `sorryAx` but does not enforce a named axiom whitelist; that report was independently inspected. The terminal precedes final assertions and no separately retained actual outer-exit receipt was found. No Lean replay or full historical/project/package/dynamic producer audit was performed.
