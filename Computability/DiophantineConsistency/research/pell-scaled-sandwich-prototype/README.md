# Lower Pell sandwich with scaled, shifted bases

`PellScaledSandwich.lower_of_gap` proves the lower variable-base Pell ratio sandwich in every IΣ₁ model from an explicit coefficient inequality and a positive internal index. `shifted_coefficient` proves the relevant polynomial inequality for the 80 graph's scaled bases `S*(X+1)−1` and `2*(X*S²−1)+1`, for any positive natural `X,S`. Both use the represented variable-base power and existing internal Pell growth bounds.

Guarded author `observations/attempt02/` passed without diagnostics, yielding `/tmp/pell-scaled-sandwich-4og0a_i2/PellScaledSandwich.olean`, SHA-256 `8c4e99044409e21d65870fd802dd254d0a75c0c8aaf2111a5019a72bc919dc0b`; attempt01 checked an earlier one-theorem source. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. Selected prototype objects and the direct sandwich provider are pinned, not complete project/package/dynamic or historical source-object ancestry. Resource checks are sampled; no paired replay is claimed.

This is only the lower sandwich and its coefficient gap. The graph binding, upper sandwich, half-binomial rounding, machine reconstruction, and iPRA endpoint remain separate.
