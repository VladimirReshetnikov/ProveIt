# Cancel the graph H factor modulo μ²

`Direct80CarrierCancelH.graph_cancel_H` proves in every IΣ₁ model that an actual positive zero of the exact Lean 80-row graph with positive beta satisfies `μ² ∣ h*e` in the difference ring, for the graph's actual `μ`, `h` and signed `e`. It starts from the independently checked certificate `μ² ∣ h*H*e` and cancels the graph factor `H` using its exact polynomial form `H=μ*t-1`. The generic ring lemma constructs an explicit inverse modulo `μ²`; no parity, rank sign, fixed-port or coprimality assumption is needed.

The remaining factor `h` is **not** canceled. Its cancellation requires a separate valid unit certificate, obtained only after radix parity is established. This is not yet a graph-to-halt or iPRA endpoint.

Guarded author `observations/attempt02/` passed without diagnostics, yielding `/tmp/tenpositive-80carrier-cancel-h-t2c1c_6v/Direct80CarrierCancelH.olean`, SHA-256 `83d3dbdb38aa748e1418b630e347c56073fcd3c7f92b6e90021969d36d8ca5f2`; attempt01 compiled with linter warnings and was rejected by the runner. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. Selected prototype objects and one inherited provider are pinned, not the complete project/package/dynamic or historical source-object ancestry. Resource checks are sampled; no paired replay is claimed.
