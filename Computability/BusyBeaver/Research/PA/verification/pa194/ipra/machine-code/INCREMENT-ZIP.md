# Literal-machine increment execution

`PA194IncrementZip.literalIncrement` runs the pinned literal `M6.Zip` machine
from an actual configuration whose dense control is 2, whose left tape is an
arbitrary finite list, and whose right tape is the imported
`M6.Runtime.sepsM` marked-file layout. For any finite prefix and suffix of
natural-valued registers, after the explicit primitive-recursive increment
clock the resulting configuration has dense control 7 and the encoded tape
halves of the imported `M6.Runtime.sepsR` layout with the selected register
incremented and a one-valued spare appended. The theorem states equality of
numeric tape encodings, which preserves the finite-support tape contents
modulo redundant far-end zeros; it does not claim list identity for zipper
representations.

This is a standard-natural-number literal execution theorem. It combines
`PA194StepperZip.modelStepperZip` with the numeric runtime specialization;
the corresponding all-model and native-iPRA arithmetic-box results are
separate and documented in `INCREMENT-ANYWHERE.md`. The proof does not show
that source execution reaches this marked entry, that the entire source
instruction is simulated, or either PA consistency implication.

Run `check-increment-zip.sh` with the pinned overlay environment described in
`MARK-ALL.md`. It rebuilds the dependencies and checks the theorem axiom
reports. Set `TMPDIR=/dev/shm` if root-disk space is limited.
