# Pell coordinates for the 80-graph projection

`Direct80ProjectionPell.graph_projection_pell` proves in every IΣ₁ model that a positive zero of the exact Lean 80-row graph, under explicit positive-beta and `MC<beta`, `MF<2*beta` port bounds, supplies the exact main Pell coordinate `d` and a natural quotient `z` satisfying `d=2^R+a*c+H*z`, `d²=1+(a²+H)c²`, and `H ∣ b*Knat`, where `R=rankNat`, `a=A−1` and `H=4A−1`. It obtains the first identity from the existing all-index Pell projection quotient and the second from the main Pell norm, with the equality `H=4a+3` proved using justified natural subtraction.

Guarded author `observations/attempt02/` passed without diagnostics, yielding `/tmp/tenpositive-80projection-pell-5jexkier/Direct80ProjectionPell.olean`, SHA-256 `f751b2cd192a1840653473585b67b10d91675ab4778a47a070a75caecc83595d`; attempt01 failed and remains recorded. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. Selected prototype objects, the direct Pell power provider, and one inherited provider are pinned, not the complete transitive project/package/dynamic or historical source-object ancestry. Resource checks are sampled; no paired replay is claimed.

This packages exact projection inputs only. The whole-product divisibility, height argument, fixed-recipe specialization, machine equivalence and iPRA endpoint remain separate.
