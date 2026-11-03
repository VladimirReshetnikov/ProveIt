# Positive integral offset quotient

`Direct80PositiveOffset.graph_positive_rho` proves in every IΣ₁ model that an actual positive zero of the exact Lean 80-row graph has a **positive natural** `rho` with signed graph offset `e=ι(μ²*rho)`, under explicit positive/odd beta and low/high port bounds. It starts with the exact post-alignment representation `e=4*firstParam*s`, proves `rankNat+1<k` from the graph's rank window and first-index lower bound, and hence proves `s>0`. The quotient retains the complete `Y²` factor; no coprimality of Y with the transport factor is used.

Guarded author `observations/attempt02/` passed without diagnostics, yielding `/tmp/tenpositive-80positive-offset-x78dpeib/Direct80PositiveOffset.olean`, SHA-256 `5331eaf3eb43b0cec181874722385f2c143029e50c1cc4f11e91fad888d8317d`; attempt01 failed and is retained. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. Selected prototype objects and one inherited provider are pinned, not the full project/package/dynamic or historical source-object ancestry. Resource checks are sampled; no paired replay is claimed.

The fixed-recipe specialization, fresh source reconstruction, graph-to-halt equivalence and iPRA endpoint remain separate.
