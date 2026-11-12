# Source-only model consecutive-square exclusion

`MainSquareGap.lean` is an **unelaborated and uncompiled source proposal**. It isolates the main-norm `k≠2` step needed by `../ordinary14-aux-root-bounds-model-draft/`; it does not extract a norm from a graph or establish any graph-zero, endpoint, provider, iPRA or external-file theorem. The dependency `Compact44.P72Root` supplies `ι_tsub`, but its direct and transitive source/object provider ancestry has not been authenticated for this draft.

The proposed `no_main_square` takes positive natural A, `1<c<2*A`, the exact natural identity `A*A=Delta+1`, and a natural square `d*d=1+Delta*c*c`. In the difference ring, the norm lies strictly between `(A*c−1)²` and `(A*c)²`: their gaps are respectively `c*(2*A−c)>0` and `c²−1>0`. The proof casts the natural predecessor `A*c−1` only after proving `1≤A*c`, pulls both square inequalities back by `ModelDifferenceRing.ι_lt_ι`, and uses model discreteness to rule out a natural d strictly between the consecutive values. The hypotheses are explicit and the subtraction in the order argument is ring subtraction.

The proposed `two_ordinate_impossible` specializes the fact to `A=X*Y+Y+2` and `c=eta+Y*(eta+zeta)` for positive X,Y,eta,zeta. If `eta+zeta=2`, positivity gives eta=zeta=1, so `c=2Y+1` and `1<c<2A`. Its `A²=Delta+1` identity and natural main norm are explicit premises. A graph client must obtain the natural square root using the positive main scale, signed magnitude and `ArithmeticAdaptiveQuotients2011.scaled_quotient`; it must also prove the exact Delta identity and bind the graph's eta, zeta and X,Y. Neither that graph extraction nor the separate bounds client is imported or proved here.

The proof scripts, ordered-ring `nlinarith`, casts, predecessor rewrite, theorem names and elaboration/resource behavior remain untested. The source inventory and finite gap controls are not a universal model proof or Lean preflight. A future run requires a coherent independently reviewed source/object/Init provider route, the established disk/resource guard and an exclusive allocation. Even after compilation, the graph-specific norm/evaluation client, `Delta<c³` polynomial bound, auxiliary root updates, compact44 and endpoint/iPRA routes remain open.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-model-main-square-gap-draft/check_source.py > /tmp/main-square-gap-source.json
cmp /tmp/main-square-gap-source.json research/ordinary14-model-main-square-gap-draft/observation.json
```

Independent source review is recorded in
`../../reviews/ordinary14-model-main-square-gap-draft-independent/`.
