# Proposed positive-gap/rank client for eta/zeta-natural probe

This source-only draft adapts the existing eta-natural first-norm, positive-C
and compact rank-window client to the exact eta/zeta-natural boundary probe.
It is unelaborated; it proves no graph-zero theorem, source/provider/axiom
replay, zero-map or internal endpoint.

The changed literal has `k=eta+zeta`, so its old automatic proof `1≤k` is no
longer valid. The proposed `gap_of_J`, `gap` and `compact_rank_window`
theorems **explicitly assume** `1≤k`; for zeta=0 this follows when eta>0,
but neither positivity nor the graph binding is supplied here. The k=0
branch requires the separate proposed double-zero obstruction. The proof
otherwise adapts the existing first-norm argument: C≤0 would make Bt<0,
then with b>0, k≥1 and natural r the exact signed first root would have a
square strictly above its norm. The signed rank-to-natural representation
and compact rank window reuse existing source interfaces, again subject to
their represented ports, casts and unelaborated providers.

The deterministic checker pins direct dependencies, checks that all three k
assumptions are explicit and exercises 107,520 finite first-norm gap
controls. It does not run Lean or establish nonstandard-model claims. From
`Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-eta-zeta-natural-gap-rank-draft/check.py | cmp - research/ordinary13-eta-zeta-natural-gap-rank-draft/receipt.json
```
