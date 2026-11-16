# First-four positive-selected blank-tail path to dense 12

`PA194FirstFourPositiveSelected.markerFirstFourPositiveBlankTo12` proves that
the first non-first marker entry with first physical value four and positive
selected value reaches dense state 12, assuming the explicit marker/file layout
and a blank final tail. The clock and final packed halves are existential model
values. This is an all-candidate-PRA-model path, not a standard-run check.

The intermediate `finishZero` and `finishSucc` theorems retain the exact output
halves for the zero and successor cases of the selected run's remaining length;
`finishSelected` combines them for arbitrary model values. These follow the
checked prefix-file return and use the state-7 return-cell and state-12-entry
contracts. The later [all-selected theorem](FIRST-FOUR-ALL-TO24.md)
continues this conditional path to state 24. Source-frame correspondence,
blank-tape reachability, and literal-machine iPRA implications remain open.

The module passed an ordered suffix replay and was also rebuilt in the full
nested machine-code chain through `check-first-four-positive-to14.sh`. That
run used retained prerequisite overlays and reported no `sorryAx`.
