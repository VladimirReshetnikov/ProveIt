# Physical marking for all nine register positions

`PA194MarkAll.modelMarkAllPositive` proves the complete physical marking run
for each non-first physical register of the pinned PA194 machine. It starts at
the corresponding runtime `sk` control, traverses the preceding regular
register blocks, changes the selected delimiter from `01` to `00`, and returns
across the prefix to native control 3 (dense 17). The number of preceding
registers is a fixed standard value 1 through 8; register and tape values may
be nonstandard in any model of classical PRA. The theorem gives explicit
primitive-recursive input and output tape codes and an exact clock. Its input
assumes the selected block begins `01`, expressed as the final prefix suffix.

`PA194MarkDelimiter.modelMarkDelimiter` separately proves the first-register
case, which has no prefix and ends at native control 1 (dense 15). Together
the two cover all nine physical register positions. The numeric file and
marker encodings have separate ordinary-natural-number bindings to the
imported runtime list layouts, documented in `INCREMENT-ANYWHERE.md`.
`PA194MarkOutputStandard.markedReturn_matches_runtime` explicitly identifies
the returned file with the imported `M6.Runtime.sepsM` layout.

`PA194MarkAllSentence.nativeIPRA` proves the eight non-first cases as explicit
universally closed primitive-recursive equations in native iPRA, with the
`01` boundary constructed directly in the input terms. The first-position
native sentence is `PA194MarkDelimiterSentence.nativeIPRA`. All these
sentences use the existing equality transfer from the proved all-model
classical PRA statements.

This is the marking routine. It does not yet establish the controller
transition from the marking exit into the increment engine, the entire source
instruction simulation, or either direction of a PA consistency reduction.

Run `check-mark-all.sh` with the pinned iPRA and Foundation overlays used by
`check-marker-prefix.sh`. It rebuilds the dependencies from the pinned inputs
and rejects `sorryAx` in printed theorem dependencies. Set `TMPDIR=/dev/shm`
if root-disk space is limited.
