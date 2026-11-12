# Proposed compact symbolic-port 84↔85 model equivalence

This unelaborated source composition specializes the generic positive 84↔85
model-zero wrapper to `CompactSymbolicPorts.ports betaNat K lowNat highNat`,
with arbitrary natural K. The actual symbolic tuple is `[beta,K,low,beta+high]`;
in particular the fourth slot is **beta plus** the high payload. The proposed
proof uses `C44Short15Facts.port_bounds` for beta positivity, beta≥46 and the
mask inequalities, `CompactFixedBeta.beta_identity` for the 590069-bit
Mersenne representation, and `P72Root.cast_port` for the four model casts.
Each direction retains its all-positive valuation and own graph zero.

This is **not a Lean-checked model theorem**. The underlying 84/85 maps,
all model and graph drafts, exact port source dependencies and provider
ancestry require guarded compilation and independent audit. The iPRA endpoint
and any correspondence to physical files, TeX or PDF remain separate. The
checker inventories the symbolic port layout and source interfaces and replays
the generic-wrapper source receipt; it does not invoke Lean.

Independent source review is recorded in
`../../reviews/ordinary14-84-85-compact-model-equivalence-draft-independent/`.
