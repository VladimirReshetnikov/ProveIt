# Zero-decrement delimiter

`PA194DecrementZeroCell.modelZeroCell` proves the seven-step selected
zero-register delimiter segment of the pinned PA194 machine in every model of
classical PRA. It starts at dense control 1 with the marked zero followed by a
nonempty next-cell boundary `0001`, and ends at dense control 11 with the
restored selected boundary and the exact half/parity relation on the left
tape. The residual tape and model values may be nonstandard. The three new
row lemmas are checked against the pinned table, and the remaining rows come
from the previously checked increment-tail work.

`PA194DecrementZeroCellSentence.nativeIPRA` proves the corresponding
universally closed primitive-recursive equation in native iPRA using the
existing equality transfer.

This covers the selected zero delimiter only. Returning across a preceding
prefix, completing the source instruction, and proving either PA consistency
direction remain open.

Run `check-decrement-zero-cell.sh` with the pinned overlay environment
described in `MARK-ALL.md`. It rebuilds dependencies and checks theorem axiom
reports. Set `TMPDIR=/dev/shm` if root-disk space is limited.
