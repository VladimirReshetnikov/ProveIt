# Separate PA194 consistency implications

`PA194OneWayEndpoint.lean` applies the separately checked one-way transfers to
the existing explicit PA194 halting sentence. `nonhalt_implies_consistency`
requires only the implication from an internal PA refutation to this machine's
halting in every candidate-PRA model with an IΣ₁ reduct; its conclusion is the
formal iPRA implication `¬Halt → Con(PA)`. The converse endpoint requires only
the implication from halting to an internal PA refutation in those models.

The `generic_*` theorems express the same two obligations in terms of the
pinned dense transition table's run in **every** IΣ₁ model, including
nonstandard times and refutations, using the all-model clock bridge. Neither
machine-specific obligation is proved here. These results do not prove either
PA194 consistency implication without its stated hypothesis.

An incremental check against the independently built transfer, certificate,
PA194 clock, and generic bridge objects passed; the four exported theorems
report `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
For a full fresh replay, set the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` as in `GENERIC-BRIDGE.md`, and run
`bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-one-way-endpoint.sh`
from the repository root. A fresh Linux run passed with the audited overlays, rebuilding the full
generic-machine and 100-module transfer/certificate chain before checking
all four endpoint theorems; no checked theorem depended on `sorryAx`.
