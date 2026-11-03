# Symbolic beta in model arithmetic

`CompactSymbolicBetaCast.beta_model` proves the fixed symbolic `betaNat` casts to `2^590069−1` in every IΣ₁ model. `beta_product` embeds the product of that beta with `rep 590069 N` into the model difference ring and proves it equals the embedding of `2^(590069*N)−1`. The proof uses the existing fixed-beta identity and generic repunit identity; it does not identify retained bytes or construct a graph zero.

The checked source SHA-256 is `eda683bf64c1f55eb698289e8f60dcb8a419212b07cdb472c83c5069b87ecfb0`. The single-author bounded check in `observations/attempt01` exited 0 with unchanged direct dependency and companion guards and no warnings or `sorryAx`. Object `/tmp/compact44-symbolic-beta-cast-author-bn288ydv/CompactSymbolicBetaCast.olean` has SHA-256 `4da9ee64cb8258c8885d9194ca48d96f3cab806d2c0e2cadefc06fe63e95fd39`. The check inherits provider/package ancestry; no full transitive/dynamic audit or paired replay is claimed.
