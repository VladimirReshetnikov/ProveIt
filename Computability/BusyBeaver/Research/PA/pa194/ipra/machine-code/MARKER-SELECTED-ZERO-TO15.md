# Selected-register-zero marker path to dense 15

`PA194MarkerZeroSelectedTo15.markerZeroTo15` follows the genuine non-first
marker-entry run when the **selected register value is zero**. This is a
different case from a zero first-block length. Starting from the exact marker
and k=1 controller layout stated in Lean, with first physical value `m+6`, it
follows the zero decrement result through dense 11, rolls back the residual
first-block run, traverses an eight-step dense-11 to dense-12 controller, and
runs the existing state-12 scanner to dense 15. The output tape halves and
model clock are explicit.

The theorem covers all eight non-first physical marker positions, every
model-valued residual `m`, and arbitrary values and following file tail,
including nonstandard values in candidate PRA models. It proves that the
returned zero-decrement file has an even code and uses that fact to match
the state-12 scanner. It does not assume a blank final suffix or `idx+n=7`.
The original marker delimiter and first-block layout remain hypotheses.

This is a conditional physical-machine execution from an intermediate marker
configuration. It does not establish blank-tape reachability, identify an
endpoint with a source frame, simulate a source instruction, or prove an iPRA
consistency implication. Further controller and layout work remains after
dense 15.

The seven new modules passed an author suffix rebuild against previously
checked prerequisite overlays, with `propext`, `Classical.choice`, and
`Quot.sound` as their reported axioms and no `sorryAx`. The full nested
checker `check-marker-selected-zero-to15.sh` is supplied but has not been run.
