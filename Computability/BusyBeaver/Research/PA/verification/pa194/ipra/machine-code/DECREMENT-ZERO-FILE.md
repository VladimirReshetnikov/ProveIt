# Zero decrement on a nonempty register file

`PA194DecrementZeroFile.modelZeroDecrementFile` connects the zero-decrement
arithmetic box to explicit all-model register-file codes. Its input is a
marked zero followed by at least one regular register, represented by the
checked file code. The proof derives the required `0001` boundary in every
candidate PRA model and identifies the output as the same zero followed by
the unchanged remaining file. The fixed prefix and suffix arities are standard
Lean naturals; their register and tape values may be nonstandard model values.

`PA194DecrementZeroFileSentence.nativeIPRA` states this stronger file-shaped
case as a universally closed primitive-recursive equation in native iPRA. Its
input terms construct the required marked zero and nonempty regular suffix.
It uses the existing equality transfer applied to the proved all-model
machine-specific equality.

The theorem starts at the physical zero-decrement entry. Source controller
and dispatch, the complete source-instruction simulation, and the PA
consistency implications remain open.

Run `check-decrement-zero-file.sh` with the pinned overlay environment
described in `MARK-ALL.md`. It rebuilds dependencies and checks theorem axiom
reports. Set `TMPDIR=/dev/shm` if root-disk space is limited.
