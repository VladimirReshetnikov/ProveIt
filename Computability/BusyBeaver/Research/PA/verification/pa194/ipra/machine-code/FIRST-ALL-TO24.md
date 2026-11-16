# Conditional first non-first marker return to state 24

`PA194FirstAllTo24.markerFirstAllTo24` proves a physical PA194 run in every
candidate PRA model, including nonstandard models. For the first non-first
marker, it covers arbitrary first-register and selected-register values,
assuming the explicitly stated intermediate tape layout and a blank trailing
field. It reaches dense state 24 with the stated left header and some right
tape. The theorem is about the pinned dense machine and its encoded stepper.

The new first-zero, positive-selected branch scans four fields, follows the
physical return over four model-length runs, and returns through the first-zero
header. The existing first-zero, zero-selected branch and the previously
checked positive-first branches complete the case split.

These statements are conditional trace components. They do not prove that the
intermediate layout is reached from the blank tape, the full controller
simulation, either machine-specific consistency reduction, or the desired
`iPRA ⊢ Con(PA) ↔ ¬Halt(M₁₉₄)` equivalence.

The new modules were checked in dependency order against retained, separately
checked prerequisite overlays. A complete run of `check-first-all-to24.sh`
also rebuilt the nested machine-code chain, and its reported theorem
dependencies did not include `sorryAx`. The replay uses the `IPRA_LEAN_OVERLAY`
and `IPRA_FOUNDATION_OVERLAY` prerequisite overlays described in this
directory's README; it does not rebuild their full transitive closure.
