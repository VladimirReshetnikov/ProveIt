# Variable-base height for the 80-row graph

`Direct80VariableHeight.graph_variable_height` proves in every IΣ₁ model that an actual positive zero of the exact Lean 80-row graph, under explicit positive-beta, `MC<beta`, `MF<2*beta` and internal odd-beta hypotheses, has an internal positive `r` with `rankNat=2r+1`, `power X r<2*(Y+1)`, and **`power X (r+1)<Hnat`**. Here `power` is represented variable-base arithmetic power and `Hnat=4A−1` is the actual natural projection divisor.

The proof checks the actual, offset Pell-base coefficient gap over the model difference ring and instantiates the independently checked variable-base paired Pell induction with the aligned first/main indices. It derives the second height bound from the first and the exact graph definitions, without invoking an unproved analytic ratio theorem or treating the two slightly shifted Pell bases as equal to earlier source bases.

Guarded author `observations/attempt03/` passed without diagnostics, yielding `/tmp/tenpositive-80variable-height-cwzviix2/Direct80VariableHeight.olean`, SHA-256 `bc6119d74b75aa9f5b99a00bd93e23588a6d653d977f697f97e3b2f05485f7cc`. Attempt01 checked an earlier weaker source; attempt02 failed during an order rewrite. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. Selected prototype objects and direct represented-power/first-index providers are pinned, not the complete project/package/dynamic or historical source-object ancestry. Resource checks are sampled; no paired replay is claimed.

This proves the divisor is larger than a variable-base power. Bounding the complete projection product below that power, applying the fixed-recipe port constraints, graph-to-halt and iPRA endpoint remain separate.
