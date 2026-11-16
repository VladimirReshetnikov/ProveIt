# Arbitrary selected value at the marker entry

`PA194AllSelectedMarkerTo24.allSelectedMarkerTo24` combines the selected-zero
and selected-positive marker paths in every candidate PRA model. From the
stated genuine non-first marker-entry configuration, it produces a later dense
state-24 configuration for arbitrary model-valued selected value `v` and
first-block parameter `k`, including nonstandard values. Both branches have
the same stated controller half; the combined theorem existentially
quantifies the clock and right tape half because the branch-specific right
halves differ.

The theorem retains the common hypotheses of the two compositions: the
non-first marker position and delimiter layout, k=1 controller header,
`idx+n=7`, blank final suffix, and first physical block `k+7`. The stronger
selected-zero branch needs neither the blank suffix nor `idx+n=7`; its exact
clock and right tape are retained in `MARKER-SELECTED-ZERO-TO24.md`. The
selected-positive zero/successor first-block cases and their exact tapes are
retained in `MARKER-INCREMENT-CONTINUE-TWO.md` and `MARKER-ZERO-CONTINUE.md`.

This is a conditional physical execution from an intermediate marker
configuration. It does not prove that configuration is reached from a blank
tape, identify the endpoints with source frames, establish source-instruction
simulation, or prove either iPRA consistency implication.

The new module passed an author suffix rebuild against previously checked
prerequisite overlays, with `propext`, `Classical.choice`, and `Quot.sound`
as its reported axioms and no `sorryAx`. The full nested checker
`check-all-selected-marker-to24.sh` is supplied but has not been run.

An independent suffix replay rebuilt the combined theorem against separately
checked zero-selected and positive-selected branch objects and retained deeper
prerequisites. It passed without `sorryAx`; this was not a full nested replay.
