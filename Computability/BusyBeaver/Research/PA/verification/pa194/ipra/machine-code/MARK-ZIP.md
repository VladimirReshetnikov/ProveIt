# Literal-machine register marking

`PA194MarkZip.literalMarkFirst` and `literalMarkPositive` run the pinned
literal `M6.Zip` machine from an actual configuration whose right tape is the
imported `M6.Runtime.sepsR` register-file layout. Together they cover all
nine physical register positions. After the explicit marking clock, they give
the resulting dense exit control and numeric tape halves matching the
imported `M6.Runtime.sepsM` marked-file layout. The initial left tape may be
any finite list, and the file consists of ordinary natural-valued registers.
The results state equality of numeric tape encodings; they do not assert
literal equality of zipper lists with possible redundant far-end zeros.

These are standard-natural-number literal execution theorems. They combine
`PA194StepperZip.modelStepperZip` with the runtime specializations; the
all-model and native-iPRA arithmetic-box results are separate and documented
in `MARK-ALL.md`. These results do not prove the controller proceeds to the
increment entry, the entire source instruction, or either PA consistency
implication.

Run `check-mark-zip.sh` with the pinned overlay environment described in
`MARK-ALL.md`. It rebuilds the dependencies and checks the theorem axiom
reports. Set `TMPDIR=/dev/shm` if root-disk space is limited.
