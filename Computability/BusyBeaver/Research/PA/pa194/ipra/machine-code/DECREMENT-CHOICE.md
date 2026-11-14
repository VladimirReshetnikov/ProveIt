# Zero-or-positive decrement in one native-iPRA equation

`PA194DecrementChoiceSentence.nativeIPRA` proves one universally closed
primitive-recursive equality for the pinned PA194 physical decrement box,
for each fixed prefix and suffix arity. The selected register may be zero or
positive, including nonstandard model values. A primitive-recursive selector
chooses the correct clock and output configuration: zero takes the checked
zero/rollback path to dense control 11 and restores the file; a successor
takes the checked positive path to dense control 7 and returns its
predecessor. The input terms construct the marked selected cell followed by a
nonempty regular file, satisfying the zero-path boundary condition.

`PA194DecrementChoice.modelDecrementChoice` is the corresponding all-model
case theorem. Its proof applies the explicit all-model zero and positive
machine contracts and uses PRA's zero-or-successor exhaustion. The native
sentence uses the existing equality transfer; it has no unproved machine-step
or branch premise.

This is the physical decrement arithmetic box with the selected register
already marked. The source controller/dispatch, complete source instruction
simulation, and PA consistency implications remain open.

Run `check-decrement-choice.sh` with the pinned overlay environment described
in `MARK-ALL.md`. It rebuilds both branch proofs and checks theorem axiom
reports. Set `TMPDIR=/dev/shm` if root-disk space is limited.
