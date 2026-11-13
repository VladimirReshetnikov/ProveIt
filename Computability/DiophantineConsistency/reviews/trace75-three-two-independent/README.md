# Independent review: trace75 main-three / first-two algebra

For any `ORingStructure V` model of IΣ₁, `Trace75ThreeTwo.graph_three_two_algebra` takes arbitrary natural ports `p`, a tuple `v : Fin 10 → V` and any model `n`. It assumes positive beta cast, all coordinates of `v` positive, and zero of the Lean trace75 `value75` at those same ports and tuple in `DiffRing V`. It also assumes the unscaled first-ordinate equality `2*ycoord n (2*(X*Y²−1)+1)=k` and **explicitly** assumes `c=ycoord 3 (A−1)`, where `A=XY+Y`.

It concludes `n=2`, `k=8*X*Y²+4`, `c+1=4*(A+1)²`, and the exact signed difference-ring identity

```
ι(eta) + 4*ι(Y)²*(ι(X)*(2*ι(Y)−ι(X)−2)−1)
  = 4*ι(Y)*(2*ι(X)+1)+3.
```

The `X,Y,k,c,A,eta` in all four conclusions are the same expressions of the same `p,v`, and `eta=v 8`. The proof obtains `n=2` from the independently reviewed `Trace75ThreeBinding` theorem, evaluates the second and third Pell ordinates under the needed positive-parameter bounds, and casts the resulting equations to `DiffRing V` before the signed ring manipulation. The subtraction in the factored expression is **difference-ring subtraction**, not natural truncated subtraction. The calculation is a consequence of the explicit main-three hypothesis, not a contradiction or its exclusion. It does not prove the missing gap/positivity condition, `r≥5`, trace74 guard, halt equivalence, iPRA theorem or external JSON/payload semantics.

`check.py` rehashes source/copies, runner, Lean binary, recorded inputs, output and logs, and resolves the direct and selected inherited objects. Its sole direct provider is reviewed `Trace75ThreeBinding` `a66ff3021153cafb70db06a89dd9ca83be49aa162c008ef9cb7e50d84da43877`; selected first paths and hashes are in `check-output.txt`. The output is `c6526cbc36bbc37365527ea028d25e46e514bca5461ef2a803e3d489725f7053`. Inner Lean exit is 0, stderr is empty and the named report is exactly `[propext, Classical.choice, Quot.sound]`. The runner rejects coded warnings/errors and `sorryAx` but does not enforce a named axiom whitelist; the captured report was separately inspected. The terminal precedes final assertions and no separately retained actual outer-exit receipt was found. No Lean replay or complete transitive/project/package/dynamic producer audit was performed.
