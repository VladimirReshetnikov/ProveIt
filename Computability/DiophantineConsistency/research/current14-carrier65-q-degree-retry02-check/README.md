# Generic Q degree: natural-cast retry

Outer session 16461 exited 0: the generic weighted-degree bound compiled and
postflight passed; the [independent terminal audit](../../reviews/current14-carrier65-q-degree-retry02-terminal-independent/)
passed. The retry replaces
the unused `Int.cast_ofNat` simplifier with
`Nat.cast_ofNat`, matching the natural cast produced by `Expr.evalRing_ofNat`.
The theorem statements remain unchanged. The no-Lean preflight and
[independent prelaunch review](../../reviews/current14-carrier65-q-degree-retry02-prelaunch-independent/)
passed; both prior failures, their absent
objects and independent audits, and direct providers remain pinned.

The intended degree-18 theorem is generic and conditional on five input
degree bounds. It does not yet establish the actual Carrier65 Q degree or
the entire expression's degree.
