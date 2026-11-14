# First-four zero-selected marker to dense state 17

`PA194FirstFourFifteenTo17.markerFirstFourZeroTo17` extends the checked
first-four zero-selected marker execution through the state-15 marker return
to dense state 17, with both packed tape halves stated exactly. The entry
retains the explicit nonempty file and header assumptions of
`markerFirstFourZeroTo15`. The theorem holds in every candidate-PRA model,
with arbitrary model-valued register contents and execution time.

The result is still an intermediate execution: it does not establish that the
marker entry is reached from blank tape, identify the returned tape as a source
frame, reach the source root, or prove an iPRA consistency implication.

The new module passed a suffix replay against the separately checked
state-15 path and retained deeper controller objects, with no `sorryAx`.
`check-first-four-zero-to17.sh` supplies the complete nested rebuild but has
not been run.
