# Proposed direct four-block rank route

The [unchecked Lean source](Trace74DirectFourBlock.lean) proposes an all-commutative-ring identity for the 74-coordinate rank. Under `q=beta*J+1`, with `MC=L`, `HP=MF-beta`, and `G=q(q-F)-C`, it states

```
R = G*(q^2-1)+(MC+q*(beta+HP))*J
  = (C-1)+(MC*J+1)+q*(F+(HP*J-1))
    +q^2*(q-C)+q^3*(q-1-F).
```

The abstract ring theorem passed the author Lean check; the [independent post-run audit](../../reviews/trace74-direct-four-block-result-independent/README.md) passed. Finite integer substitutions are diagnostic only. The identity is in a ring: converting it to the natural four-block shape requires justification of every truncated subtraction and the selected rank's natural representative.

A possible fixed-port proof route is to derive from the **74 zero itself**, with the same witnesses: `C>0`, `C<=q`, `F<q`, `HP*J>=1`, `q=Exp.exp u`, the exact natural four-block rank identity, `population(MC*J+1)+population(HP*J-1)<=u+2`, and `3u+2<=population R`. Under those explicit hypotheses, `ArithmeticSaturation.saturation` would imply `NoCarry(C-1,MC*J+1)` and `NoCarry(F,HP*J-1)`. Establishing the hypotheses directly for 74 is open: `Trace75Saturation` uses the reverse guard and cannot be imported as if it were independent.

If in addition `MC<beta`, `J>0`, and `F<=MC*J`, then `MC*J+1<q`; together with `0<C<=q`, the existing `ArithmeticRankForcing.noCarry_add_lt` would give `(C-1)+(MC*J+1)<q`, hence `C+F<q`. The needed bound `F<=MC*J` is not yet derived from a 74 zero. The [fixed-payload scalar boundary](../trace74-fixed-bfs-scalar-boundary/README.md) shows rank window and phase alone do not provide the guard; its [bit check](../trace74-fixed-bfs-nocarry-obstruction/README.md) fails the first no-carry condition, which only helps if that condition is proved necessary without the guard.

No fixed-BFS zero, guard implication, 74/75 existence equivalence or iPRA result is claimed.

The [independent source review](../../reviews/trace74-direct-four-block-draft-independent/README.md) verified the free polynomial identity and external JSON rank cone; it did not run Lean or prove natural saturation hypotheses.
