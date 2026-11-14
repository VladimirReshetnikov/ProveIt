# Increment against the imported runtime tape layouts

`PA194IncrementRuntimeStandard.runtimeIncrement` combines the PA194
physical-increment contract with the imported `M6.Runtime` list encodings.
For any finite list of preceding registers, selected register, following
registers and natural left tape, it starts at dense control 2 with the numeric
encoding of `M6.Runtime.sepsM` at the selected position. After the explicit
primitive-recursive clock it reaches dense control 7 with the numeric encoding
of `M6.Runtime.sepsR` on the same file, with the selected value incremented
and a one-valued spare appended. The exact tape-boundary convention appears in
the theorem. The input and output have blank far-right suffixes.

This is a standard-natural-number specialization; its Lean truth alone does
not establish provability in PA. The underlying arbitrary-model contract and
its explicit native-iPRA sentence are documented in `INCREMENT-ANYWHERE.md`.
This theorem is a physical arithmetic box entered with the register already
marked; it does not prove the controller reaches the increment entry, source
instruction simulation, or either consistency direction.

Run `check-increment-runtime.sh` with the pinned overlay environment described
in `MARK-ALL.md`. It rebuilds the dependencies and checks the theorem axiom
reports. Set `TMPDIR=/dev/shm` if root-disk space is limited.
