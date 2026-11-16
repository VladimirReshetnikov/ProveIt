# Marked-register increment after an arbitrary finite prefix

`PA194IncrementAnywhere.modelIncrementAnywhere` gives a checked arithmetic-box
contract for the pinned PA194 transition table. For each fixed standard choice
of `p` prefix registers and `n` registers following the marked register, it
holds in every model of classical PRA, including models with nonstandard tape
halves and register values. The clock and every encoded tape operation are
explicit primitive-recursive codes. The physical run starts in dense state 2
at the first prefix block; after the stated number of steps it reaches dense
state 7 after returning across the prefix. It increases the marked register by
one, preserves the prefix and remaining regular blocks, and appends the
one-valued spare described in `INCREMENT-RETURN.md`. Its precise output has the
half/parity convention of the returned tape boundary.

`PA194IncrementAnywhereStandard.markedFile_matches_runtime_anywhere` also
identifies the input, over ordinary natural numbers, with the imported
`M6.Runtime.sepsM` list layout at the selected position.
`PA194IncrementOutputStandard.incrementOutput_matches_runtime` identifies the
returned file with `M6.Runtime.sepsR` on the unchanged prefix, the incremented
entry, the unchanged suffix, and a final register of value one.

The theorem assumes that the prefix's tail is exactly the separately encoded
marked file and that this marked file ends with a zero tape suffix. Those are
actual premises, not consequences of a physical blank-tape startup. The term
`returnCode` used in the output is shown equivalent to the ordinary file code
with its suffix replaced in `PA194ReturnFileMeaning.modelReturnMeaning`.

`PA194IncrementAnywhereSentence.nativeIPRA` proves a family of universally
closed equations in native intuitionistic PRA. Its input terms build the
prefix-to-marked-file connection and zero suffix directly into the sentence;
it is obtained from the proved all-model result through the existing explicit
classical-PRA-to-iPRA equality translation. The fixed arities are Lean natural
numbers; the theorem does not assert traversal of a nonstandard number of
register blocks.

The proof does not establish how the source engine marks a register, executes
binary instruction dispatch, or returns to the next source configuration, nor
does it prove either direction of the PA consistency reduction. The cited
standard source-file bindings and the physical/logical permutation are in
`REGISTER-FILE.md` and `SOURCE-FILE-ENGINE.md`.

Run `check-increment-anywhere.sh` with the same pinned overlay environment as
`check-increment-return.sh`; it rebuilds all dependencies in a temporary
directory, checks the pinned inputs, and rejects `sorryAx` in printed theorem
dependencies. Set `TMPDIR=/dev/shm` if temporary disk space is limited.
