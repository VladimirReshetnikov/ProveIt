# The `10111111` controller transition

`PA194ContinueTwoDispatch.continueTwo32` proves an exact 32-step transition
for the pinned dense PA194 table in every candidate PRA model, including
nonstandard model-valued `u` and `r`. In ordinary arithmetic notation it is

```
(control, left, right) = (24, 512*u + 1, 256*r + 253)
                       → (24, 512*u + 1, 256*r + 61).
```

The theorem uses nested additions and the `ones` and `zeros` function codes
rather than the multiplication shorthand. The low eight right-hand cells,
listed head first, change from `10111111` to `10111100`; all higher cells and
the left half are preserved. The proof composes previously checked 3-, 6-,
5-, and 18-step runs, and proves that their model clock equals the numeral 32.

This is a conditional physical-machine theorem. It does not establish that
its input is reached from the blank tape, that `u=0`, or that the tape has
any particular source-register contents. For `u=0` and the other explicit
root-frame hypotheses in `SEVEN-TO-ROOT-CONTROL.md`, the input and output
patterns are consistent with a source-frame change from `10111111` to the
zero extension `10111100`. The pinned source-tree data identify the former
path as `continueTo 2` and the leaf `1011110` as `dec 6`; these source-tree
identifications and the jump between them are now checked in
[`PA194SourceFacts`](../../../pa194-source-tree/PA194SourceFacts.lean).
The physical theorem does not prove the dense/native source-frame correspondence
and is not an iPRA derivation or a PA consistency equivalence.

An author suffix rebuild of the new module passed against separately checked
prerequisite overlays, with `propext`, `Classical.choice`, and `Quot.sound`
as its reported axioms and no `sorryAx`. The reproducible full nested checker
`check-continue-two-dispatch.sh` was prepared but has not been run.

An independent suffix replay rebuilt the 32-step module against the separately
checked return-to-control path and retained deeper prerequisites. It passed
without `sorryAx`; this was not a full nested replay.
