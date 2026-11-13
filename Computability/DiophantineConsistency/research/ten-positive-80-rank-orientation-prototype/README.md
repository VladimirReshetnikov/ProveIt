# Actual graph rank is positive

`Direct80RankOrientation.graph_rank_positive` proves in every IΣ₁ model that a positive zero of the exact Lean 80-row graph with positive beta has positive signed graph rank `rExpr`. It uses the independently established nonnegative transport/mask gap, rather than assuming a rank sign. The proof shows the first rank summand is strictly positive and the second is nonnegative for arbitrary natural remaining ports.

The guarded author check `observations/attempt01/` succeeded without diagnostics, producing `/tmp/tenpositive-80rank-orientation-1osgudwp/Direct80RankOrientation.olean`, SHA-256 `c29c0fea46cd5ad4590fe796348887465e9f0e97feb6357e00c494f4e9f2bfa8`. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. Selected prototype objects and one inherited provider are pinned, while full transitive project/package/dynamic and historical source-object ancestry remain inherited. Resource observations are sampled; no paired replay is claimed.

This establishes orientation only. The fixed-port rank window, its smallness relative to `c`, main-index equality, machine theorem and iPRA endpoint are separate.
