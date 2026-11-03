# Signed integral carrier for actual 80-graph zeros

`Direct80SignedCarrier.graph_signed_carrier` proves in every IΣ₁ model that an actual positive zero of the exact Lean 80-row graph with positive beta has the positive roots and adjacent-Pell data from `graph_adjacent`, and a difference-ring carrier `z=±ι(τ*f*y)` satisfying `Z=ι(M)*z` and `z≤ι(τ*f*y)`. The proof factors equality of squares in the model difference ring; it makes no choice of the sign of `Z`, `z`, rank, or transport factor. All roots and the adjacent norm belong to the same witness tuple.

Guarded author `observations/attempt01/` passed without diagnostics, yielding `/tmp/tenpositive-80signed-carrier-qxxj6q7r/Direct80SignedCarrier.olean`, SHA-256 `8e3395ca680a799ee1a9e8a9fc82191016593f756851f9d58747df7f0612965a`. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. The runner pins selected prototype objects and one inherited provider, not the complete transitive project/package/dynamic or historical source-object ancestry. Resource observations are sampled; no paired replay is claimed.

This establishes signed carrier integrality only. The one-sided size estimates and their application to transport, graph-to-halt equivalence, and an iPRA proof remain separate. External graph/PDF correspondence is also separate.
