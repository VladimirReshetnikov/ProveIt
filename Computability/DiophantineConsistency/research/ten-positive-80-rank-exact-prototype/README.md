# Exact graph rank is the odd main Pell index

`Direct80RankExact.graph_rank_exact` proves in every IΣ₁ model that a positive zero of the exact Lean 80-row graph has a positive natural rank that is the **actual odd main Pell index**: `rankNat % 2=1` and `c=ycoord rankNat (A-1)`. Under the explicit natural port assumptions `beta>0`, `MC<beta`, and `MF<2*beta`, it also records `24≤rankNat` and the stronger upper window `rankNat+q³+q+1≤q⁴`.

The proof connects the exact signed graph expression to `rankNat`, matches the separately checked window's differently ordered natural formula, uses the graph-specific bound `2q⁴<c` to discharge the conditional smallness of **every** signed-pair representation, and invokes the checked rank equality theorem. Equality of natural rank and signed-pair magnitude is proved via injectivity of the model difference-ring embedding. No rank sign or main-norm assumption is imposed.

Guarded author `observations/attempt04/` passed without diagnostics, yielding `/tmp/tenpositive-80rank-exact-vv74z58l/Direct80RankExact.olean`, SHA-256 `340c2d3996a9a3eb04cc054ffa055b56845363738800ead2275d5848734b9e1c`. Attempts 01–03 failed during elementary bound elaboration and remain recorded. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. The runner pins selected prototype objects, the direct rank-window provider and one inherited provider; full transitive project/package/dynamic and historical source-object ancestry remain inherited. Resource checks are sampled; no paired replay is claimed.

The two explicit port bounds still need to be tied to a chosen fixed byte recipe. First/main index alignment, whole-product projection, graph-to-halt equivalence, the iPRA endpoint and external graph/PDF correspondence remain separate.
