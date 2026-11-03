# Independent review: generic main-index-three exclusion for large first index

The frozen accepted generic theorem `Trace75ThreeLarge.impossible` works in any `ORingStructure V` model of IΣ₁. It quantifies over arbitrary model `X,Y,k,eta,n`, assumes `2≤X`, `2≤Y`, `0<eta`, `3≤n`, and both equations

```
2*ycoord n (2*(X*(Y*Y)−1)+1) = k,
k*Y+eta = ycoord 3 ((X*Y+Y)−1),
```

and concludes `False`. It has no graph-zero, port or external coefficient premise. The proof takes `P=XY²`, `A=XY+Y`, establishes `A+1≤P` with the explicit X/Y bounds, uses monotonicity of the first Pell ordinate and the exact third-ordinate formula to get `2*(C+1)≤k+2`, while `C=kY+eta>k` makes the reverse strict inequality hold. Natural subtractions in both chart parameters are justified by positivity. The theorem excludes main index three only when the first index is **at least three**; it does not handle `n=2`, establish a graph binding, halt equivalence, trace74 guard or iPRA result.

`check.py` rehashes the source/copies, runner, all pinned inputs including Lean, object and logs; resolves the two direct arithmetic/tactic imports through the recorded search path; and checks the retained failed attempts. Exact selected paths and hashes are in `check-output.txt`. Accepted attempt05 has inner exit 0, object `d8e8d07e7b91ee60a8afe6ea393f839f9c49aa386185d134d2bdefee8ca7b604`, exactly `[propext, Classical.choice, Quot.sound]` in its named report, and empty stderr. Attempts01–04 all had nonzero Lean exits and are not accepted. The runner rejects coded diagnostics and `sorryAx` but does not enforce a named axiom whitelist; the report was independently inspected. Its terminal precedes final assertions; no separately retained actual outer-exit receipt was found. No Lean replay or full transitive/project/package/dynamic producer audit was performed.
