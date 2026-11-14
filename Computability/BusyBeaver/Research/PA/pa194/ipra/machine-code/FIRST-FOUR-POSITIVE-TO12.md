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
contracts. The dense-24 return, source-frame correspondence, blank-tape
reachability, and literal-machine iPRA implications remain open.

The new module passed an ordered suffix replay against the separately checked
first-four positive-return path and retained deeper controller objects, with
no `sorryAx`. `check-first-four-positive-to12.sh` specifies a full nested
rebuild but has not been run.
