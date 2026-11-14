# Positive-decrement delimiter

`PA194DecrementPositiveCell.modelPositiveCell` proves the exact four-step
selected-delimiter segment of the pinned PA194 physical positive-decrement
routine in every model of classical PRA. It starts at dense control 1 with
the marked positive-register boundary `001` and an arbitrary residual tape;
it ends at dense control 7, preserving the left tape and changing the
boundary to the expected positive-decrement form. Tape values may be
nonstandard. The proof checks the remaining dense-4 transition and composes it
with previously checked rows and the explicit primitive-recursive stepper.

`PA194DecrementPositiveCellSentence.nativeIPRA` proves the corresponding
universally closed primitive-recursive equality in native iPRA using the
existing equality transfer.

This is only the selected delimiter in the positive case. It does not yet
compose the prefix traversal and return, cover a zero register, establish a
complete source instruction or prove a consistency reduction.

Run `check-decrement-positive-cell.sh` with the pinned overlay environment
described in `MARK-ALL.md`. It rebuilds dependencies and checks theorem axiom
reports. Set `TMPDIR=/dev/shm` if root-disk space is limited.
