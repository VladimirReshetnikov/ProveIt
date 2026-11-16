# Zero-register decrement and rollback

`PA194DecrementZero.modelZeroDecrement` proves the complete zero-register
physical arithmetic box for the pinned PA194 table in every model of
classical PRA. It starts at dense control 1, crosses an arbitrary fixed finite
prefix of regular blocks, executes the seven-step marked-zero delimiter, and
rolls the prefix back to dense control 11. The input explicitly assumes a
nonempty following cell, expressed by the low-bit boundary `0001`. The output
restores the selected zero and all prefix blocks, with the exact half/parity
tape convention. The clock and file operations are explicit
primitive-recursive codes; register and residual tape values can be
nonstandard in a candidate PRA model.

`PA194DecrementZeroSentence.nativeIPRA` proves the corresponding universally
closed primitive-recursive equation in native iPRA for each fixed prefix
arity. Its input terms construct the required following-cell boundary. The
proof uses the checked all-model rollback scanner, boundary transitions and
prefix composition, followed by the existing equality transfer.

This is a physical arithmetic box entered with the selected register already
marked. It does not establish source controller/dispatch, a complete source
instruction simulation, or either PA consistency implication.

Run `check-decrement-zero.sh` with the pinned overlay environment described
in `MARK-ALL.md`. It rebuilds dependencies and checks theorem axiom reports.
Set `TMPDIR=/dev/shm` if root-disk space is limited.
