# Independent review: main index three implies first index two

For any `ORingStructure V` model of IΣ₁, the accepted `Trace75ThreeBinding.first_index_eq_two_of_main_three` takes arbitrary natural ports `p`, an arbitrary tuple `v : Fin 10 → V`, and **any** model index `n`. It assumes positive beta cast, all coordinates of `v` positive, and zero of Lean's trace75 `value75` at those same ports/tuple in `DiffRing V`; additionally it assumes both

```
2*ycoord n (2*(X*Y²−1)+1) = k,
c = ycoord 3 (A−1),   A=X*Y+Y.
```

It concludes `n=2`. The proof applies the reviewed universal graph-specific bound `2≤n`, derives `X,Y≥2` from the actual positive inputs, and rules out `n≥3` with the independently reviewed generic `Trace75ThreeLarge.impossible`. It uses the same `p,v,n` throughout and the unscaled `X*Y²` first parameter. The main-ordinate equation at index three remains an **explicit hypothesis**. In particular, this packet does not exclude index three: the first-index-two case remains, and no `r≥5`, halt equivalence, trace74 guard, iPRA or external file-binding conclusion follows.

`check.py` rehashes source/copies, runner, Lean binary, all recorded pinned inputs, object and logs, and checks first resolution of both direct providers. They are reviewed `Trace75Index` `6cc75eb28726516d4901542f26f083ecceeb682d459ff4a71022f3d88b1a3a34` and `Trace75ThreeLarge` `d8e8d07e7b91ee60a8afe6ea393f839f9c49aa386185d134d2bdefee8ca7b604`; exact selected paths are in `check-output.txt`. The output is `a66ff3021153cafb70db06a89dd9ca83be49aa162c008ef9cb7e50d84da43877`. Its inner exit is 0, stderr empty, and sole named report exactly `[propext, Classical.choice, Quot.sound]`. The runner rejects coded diagnostics and `sorryAx` but does not enforce a named axiom whitelist; this review checked the report separately. Its terminal precedes final assertions, and no separately retained actual outer-exit receipt was found. No Lean replay or complete transitive/project/package/dynamic producer audit was performed.
