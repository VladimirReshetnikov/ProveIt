# Uncompiled terminal-agreement bridge draft

This source-only client adapts `static_terminals_agree` from `../nine-sharing-norm38-reference-draft/Norm38Reference.lean` to use the checked `reference_gate_equations_batched` theorem. Under `gatesHold` in an IΣ₁ model, it proposes to combine the checked static-assignment fixed point, checked generic topological replay, checked concrete graph topology and checked 60 reference-gate equations to identify the six static terminal values with the corresponding reference nodes.

The `Norm38ReferenceInitial` import remains unavailable: the single-module initial-agreement check timed out, and a split fallback is being prepared. Consequently this client has no authenticated complete provider and has not been compiled. Its list-completion `decide` proofs and source elaboration may require further factoring. A success would provide the terminal-agreement premise for the separately checked conditional static-to-carrier theorem, not the reverse construction or iPRA endpoint.

The draft source SHA-256 is `73db8a51b7dbaa0681643f223f643e2d91bc24ee3c4277ab86828944d62a1c57`. No Lean runner or compiled object is claimed.
