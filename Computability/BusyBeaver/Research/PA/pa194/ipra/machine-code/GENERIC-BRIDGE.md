# PA194 generic machine step bridge

`PA194GenericBridge.pointwise` proves equality of the pinned PA194 packed
step and `ConPA.Machine.step` for every configuration in every candidate PRA
model whose arithmetic reduct satisfies IΣ₁. It applies to nonstandard
configurations. Controls at least 194 are shown to stutter in both machines.
The table is built directly from the generated pinned PA194 rows, and lookup
correctness is proved uniformly rather than by assuming a second copy of the
transition table.

`PA194HalfDiv` separately identifies the tape half and parity functions with
division and remainder by two in every candidate PRA model. This result only
uses open induction and covers nonstandard arguments.

`PA194Reachable` checks that all generated target controls are at most 194 and
uses internal open induction to prove that the packed clock has control at most
194 at every model time. Consequently its halt indicator is one exactly at
control 194, again in every candidate PRA model and at nonstandard times.

`PA194GenericHalt.clockRun` uses the unary coded-history graph to identify the
packed clock with the generic run at **every** model time in candidate PRA
models whose arithmetic reduct satisfies IΣ₁, including nonstandard times.
`haltEquiv` proves the corresponding model equivalence between the packed halt
indicator existential and the generic arithmetic halt sentence. `sentenceBridge`
connects this to the existing `PA194ExplicitEndpoint.haltClassical`.

`PA194GenericHalt.endpoint` proves, **conditional on** `Calibrated denseTable
194`, that standard iPRA proves `Con(PA) ↔ ¬haltSentence` for the existing
PA194 halt sentence. Calibration asserts that in every IΣ₁ model, internal
PA refutability is equivalent to this generic machine reaching state 194; its
proof is still open. The endpoint does not establish either consistency
direction without that hypothesis.

To replay, use the same pinned overlays as `check-mark-all.sh` and run
`bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-generic-bridge.sh`
from the repository root. The script builds the generic machine from source and uses a private temporary
directory for the generated PA194 rows and all other local dependencies.

An independent fresh Linux replay through `check-one-way-endpoint.sh` also
rebuilt this complete generic bridge and the 100-module transfer/certificate
chain successfully, with no `sorryAx` in the checked theorem dependencies.
