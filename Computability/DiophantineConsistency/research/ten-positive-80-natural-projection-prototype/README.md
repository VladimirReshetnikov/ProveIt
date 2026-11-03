# Natural projection divisor for actual graph zeros

`Direct80NaturalProjection.graph_natural_projection` proves in every IΣ₁ model that an actual positive zero of the exact 80-row Lean graph with positive beta satisfies the **natural** divisibility `Hnat ∣ b*Knat`, where `Hnat=4A−1` and `Knat=X*(3c−2X)+2`. It starts from the signed difference-ring projection divisor, uses the checked graph gap `2X<3c` and positivity of `A` to justify both natural subtractions, and transfers divisibility back to the natural model. The generic transfer handles a signed quotient by splitting its two possible signs and does not assume the quotient positive.

Guarded author `observations/attempt02/` succeeded without diagnostics, yielding `/tmp/tenpositive-80natural-projection-4ullun5w/Direct80NaturalProjection.olean`, SHA-256 `66c2286a5a26d86cf3dc1dc043a4bcaf3826dbc52ec2e7b8ea93fc33a7407e3e`; attempt01 failed and is retained. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. Selected prototype objects and one inherited provider are pinned, but complete project/package/dynamic and historical source-object ancestry remain inherited. Resource checks are sampled; no paired replay is claimed.

The full-product projection, fixed-recipe integration, graph-to-halt equivalence, and iPRA proof-existence endpoint remain separate.
