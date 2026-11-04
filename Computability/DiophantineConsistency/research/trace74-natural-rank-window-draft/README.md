# Conditional natural rank and window without the sum guard

The two Lean-checked clients establish a natural representative and its window under **individual** bounds, without assuming `F+C<q`. For model values with `q=beta*J+1`, `beta≥31`, `J>0`, `0<F<q`, `0<C≤q`, and `MC<beta<MF<2*beta`, define

```
R = (q*(q-F)-C)*(q²-1) + (MC+q*MF)*J.
```

`Trace74NaturalRankWindow.scalar_window` proves `3*q<R` and `R+q³+q+1≤q⁴`. `Trace74RankBinding.graph_rank_eval` proves that the signed rank of the 74-induced difference-ring valuation equals `ι R`, needing only `F<q` and `C≤q`. `ring_rank_shape` supplies its all-commutative-ring identity. No graph-zero hypothesis is used by these lemmas, and no graph zero is shown to imply the individual bounds. Thus the 74 guard, equivalence and iPRA endpoint remain open.

The two-stage author retry passed actual session 89234, exit 0 and fully reaped. Terminal SHA-256 `6c9872729041fb631e8005c3b7b1c898ecc2702ffc33c8d46aeff01a107e5c24`; output directory `/tmp/trace74-natural-rank-b72_2s9a/lib`; window object `0deddd45225a1522fddef89f1505a164c6e88b82dadecd427cebb46fc55b6ca4`, binding object `5bb71e09d5dfdce5e0d4660062a0aff7a9b26d7e1e0e6f3581382cd7c825b1b2`. The three reports use only `propext`, `Classical.choice`, `Quot.sound` as applicable. The [independent result audit](../../reviews/trace74-natural-rank-window-result-independent/README.md) passed (SHA-256 `1f07348e42cd35b11c42e53e9b0257744dede8d1b8596cbd7b554d73277ced29`). Direct pins do not prove full project/package/dynamic ancestry or monitored first-resolution.

Attempt01 is preserved: stage1 passed, stage2 had two sorry-free reports but exited 1 because a final `ring` followed a tactic that closed its goal. The corrected source removes only that extra tactic; its [partial-result/retry prelaunch review](../../reviews/trace74-natural-rank-window-retry-prelaunch-independent/README.md) records the distinction. The subsequent `Trace74NaturalRankCongruence.lean` is a separate unchecked draft and is not part of the above checked result.
