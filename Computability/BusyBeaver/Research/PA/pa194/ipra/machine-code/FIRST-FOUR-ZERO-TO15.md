# First-four zero-selected marker to dense state 15

`PA194FirstFourZeroTo15.markerFirstFourZeroTo15` proves that the first
non-first marker position reaches dense state 15 when the first physical value
is four and the selected value is zero, under its explicit nonempty file and
header hypotheses. The final packed tape halves are stated exactly; the clock
may be nonstandard. The proof composes the previously checked path to dense 61,
the zero-selected return to dense 84, and its scan to dense 15 in every
candidate-PRA model.

This is a conditional intermediate execution. It does not show that the
starting tape is reachable from blank tape or identify a source frame. Its
state-15 left header differs from the existing first-five return contract, so
that contract does not directly establish a return to dense 24. Neither iPRA
consistency implication follows.

A suffix replay rebuilt the new module against retained first-four and
separately checked earlier controller objects, without `sorryAx`.
`check-first-four-zero-to15.sh` specifies a full nested rebuild but has not
been run.
