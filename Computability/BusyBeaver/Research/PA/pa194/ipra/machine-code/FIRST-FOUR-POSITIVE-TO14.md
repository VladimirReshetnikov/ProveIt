# First-value-four positive marker return through state 14

`markerFirstFourPositiveBlankTo14` in `PA194FirstFourPositiveTo14.lean`
continues the physical-table run from the first non-first marker to dense
state 14. It assumes first register value four, a positive selected value,
the stated marker layout, and a blank tail after the fixed finite file.
The proof holds in arbitrary candidate-PRA models, including nonstandard
register lengths and run times.

The returned file is shown to have an even tail; consequently both the zero
and successor remaining-selected cases reach state 13 with an even right tape
half. The next physical transition then reaches state 14. The proof witnesses appear in `PA194FirstFourPositiveTo13.lean`; the theorem
statements retain existential tape halves.

Lean compiled this module against previously checked prerequisite objects and
reported no `sorryAx`. The nested replay wrapper was syntax checked but not
run for this change. This does not establish blank-start reachability,
source-frame simulation, or either consistency implication for the literal
machine.
