# Simple natural radix and rank lower bounds

`Direct80RankLower.rank_ge_radix` proves in every IΣ₁ model that the exact natural graph rank is at least `q`, assuming only positive beta, `J`, and alpha. `graph_rank_lower` strengthens this to `q≥32`, `X≥32`, and `rankNat≥32` under the explicit hypothesis `beta≥31` and positive `J`, alpha, and `w`. `h_lt_X` proves `b<X` from positive `w`, with no graph-zero hypothesis. `half_rank_ge_fifteen` shows that `R≥32` and `R=2r+1` imply `r≥15`.

Guarded author `observations/attempt03/` passed without diagnostics, yielding `/tmp/tenpositive-80rank-lower-nc7vl_c0/Direct80RankLower.olean`, SHA-256 `317c0619b647d15f16cfa51455574b88822fb39225a66eb5cbee12a00064a960`. Attempt01 failed and attempt02 checked an earlier source. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. The runner pins selected prototype objects and one inherited provider; complete project/package/dynamic and historical source-object ancestry remain inherited. Resource checks are sampled; no paired replay is claimed.

These are elementary graph-expression inequalities, not a fixed-recipe lower-bound certificate, full-product height theorem, machine theorem, or iPRA endpoint.
