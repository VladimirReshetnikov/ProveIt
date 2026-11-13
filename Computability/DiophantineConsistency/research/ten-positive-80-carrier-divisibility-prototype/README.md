# Carrier supplies a signed divisibility certificate

`Direct80CarrierDivisibility.graph_carrier_divisibility` proves in every IΣ₁ model that a positive zero of the exact 80-row Lean graph with positive beta satisfies `μ² ∣ h*H*e` in its difference ring. Here `h`, `H`, `μ`, and signed `e` are evaluations of the actual graph syntax. It uses the signed integral carrier and the exact ring carrier identity to construct a quotient explicitly. The result requires no parity, rank sign, transport sign, coprimality, or fixed-port bounds.

The theorem deliberately does **not** cancel `h*H`: obtaining `μ² ∣ e` requires an additional valid unit or coprimality certificate, including the radix parity step. This is not a graph-to-halt or iPRA endpoint.

Guarded author `observations/attempt02/` passed without diagnostics, producing `/tmp/tenpositive-80carrier-divisibility-1cwqtt2k/Direct80CarrierDivisibility.olean`, SHA-256 `5ecb7df284acff373a9b852f8cd3b9f8b6f30a1d9ad28ce11615c89d92ee6024`; attempt01 failed and is retained. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. The runner pins selected prototype objects and one inherited provider, not full transitive project/package/dynamic or historical source-object ancestry. Resource checks are sampled; no paired replay is claimed. External JSON/source and displayed-file correspondence remain separate boundaries.
