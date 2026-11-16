# Marker returns with first physical value `m+5`

`PA194FirstAtLeastFiveTo24.firstAtLeastFiveTo24` combines the first-value-five,
first-value-six, and first-value-`k+7` marker paths using model
zero/successor exhaustion. In every candidate PRA model, for every
model-valued `m` and selected value, it reaches dense state 24 from the
stated non-first marker-entry configuration when the first physical value is
`m+5`. It covers all eight non-first marker positions and includes nonstandard
model values and clocks. The endpoint has the common stated controller half;
the clock and right tape half are existentially quantified. The separate
branch theorems retain their exact tape equations.

The theorem retains the common marker delimiter and nonempty following-file
layout, k=1 controller header, `idx+n=7`, and blank final suffix hypotheses.
The first-five and first-six branch theorems have weaker conditions. No
machine invariant here proves that reachable marker configurations satisfy
the `m+5` condition or these other hypotheses. The existing threshold split
classifies first values 0–4 separately, but their later paths are not covered
by this theorem and their reachability has not been established here.

This is a conditional physical-machine result. It does not establish
blank-tape reachability, identify the endpoint as a source frame, prove
source-instruction simulation, or prove an iPRA consistency implication.

The new module passed an author suffix rebuild against previously checked
prerequisite overlays, with `propext`, `Classical.choice`, and `Quot.sound`
as its reported axioms and no `sorryAx`. The full nested checker
`check-first-at-least-five-to24.sh` is supplied but has not been run.

An independent suffix replay rebuilt the combined theorem against separately
checked first-five, first-six and larger-first-value branches. It passed
without `sorryAx`; this was not a full nested replay.
