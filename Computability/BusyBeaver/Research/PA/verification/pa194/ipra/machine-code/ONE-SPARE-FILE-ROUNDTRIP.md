# Model-length one-valued spare-file carry

`PA194OneSpareIterate` defines a primitive-recursive code for iterating a
one-valued block a model-valued number of times. `modelFullCarry` proves the
literal machine's state-3 carry across that many such blocks, in every model of
PRA and with an arbitrary remaining tape. Its proof uses model open induction:
the block count can be a nonstandard model element. The exact clock is `3*n`.
`PA194OneSpareIterateSentence.nativeIPRA` expresses this forward traversal as
an actual universally quantified native iPRA derivation in `standardTheory`;
this is the native standard theory used by the existing PRA-to-iPRA transfer,
not an appeal to Lean proving consistency.

`PA194OneSpareReturn` proves the reverse traversal by model open induction,
again for model-valued count, with exact clock `3*n`. The next modules compose
the blank-end exit and return and identify the resulting file. The theorem
`PA194OneSpareFileRoundTrip.roundTrip` starts in state 3 on an odd marked
left cell, followed by a model-valued spare block and `n` one-valued trailing
blocks, with a blank far end. It ends in state 7 with the specified marked
cell return and the same spare block followed by `n+1` one-valued blocks.
Both `n` and the spare value are arbitrary elements of the PRA model. The
full nested primitive-recursive clock and exact tape expressions are in the
statement. The marked-cell value need only be odd. This theorem does not
cover an arbitrary sequence of varied trailing blocks, or a nonblank far
end; nor does it prove a complete source instruction, an unbounded machine
simulation, nonhalting, or either consistency implication.

Replay into a new output directory with ordinary git environment:

```sh
check-one-spare-file-roundtrip.sh REPO SITE27_BASELINE SITE28_STAGE ROUND_STAGE PROJECT PACKAGE SOURCE_DIR NEW_OUTPUT
```

The checked invocation used `SITE27_BASELINE=/dev/shm/pa194-site27-coherent/build`,
`SITE28_STAGE=/dev/shm/pa194-site28-work/build-carry-seven`,
`ROUND_STAGE=/dev/shm/pa194-site28-work/build-carry-roundtrip`,
`PROJECT=/tmp/current14-standard-fresh-build-20261104/lib`, and
`PACKAGE=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`. It rebuilds the
three carry-code prerequisites and all new modules from the pinned source, checks
for `sorryAx`, verifies immutable machine-object inputs, and rejects fallback
machine objects in general library roots. The baseline, stage and round objects
remain retained staged inputs; this is an incremental replay, not a fresh
rebuild of their transitive source closure.
