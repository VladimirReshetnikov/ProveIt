# Marker prefix traversal and selected delimiter

`PA194MarkerSkip.modelMarkerSkipCell` checks one regular-register skip for each
of the eight nonzero PA194 marker-entry controls, with arbitrary model-valued
register and tape data. `PA194MarkerPrefix.modelMarkerPrefix` composes those
skips for each fixed prefix length 0 through 8. Its initial control is the
corresponding marker entry; it ends at native state 51 (dense 113) at the
selected delimiter. The clock and accumulated tape are explicit
primitive-recursive codes.

`modelMarkerPrefixAndDelimiter` composes this traversal with the separately
checked three-step delimiter erasure. It assumes that the suffix after the
prefix begins `01` and ends at native state 1 (dense 15), with the delimiter
marked and the exact resulting half/parity tape boundary. Both the register
values and tape data may be nonstandard in a candidate PRA model; the number
of registers is one of the nine standard syntactic choices.

`PA194MarkerSkipSentence.nativeIPRA` and `PA194MarkerPrefixSentence.nativeIPRA`
provide the corresponding universally closed primitive-recursive equations in
native iPRA. The latter constructs the selected `01` boundary in the input
terms. These are derived from the machine-specific all-model theorems using
the existing classical equality transfer.

For non-first positions the run must still return across the prefix to finish
marking. The controller transition into the increment engine and the source
instruction/consistency reductions also remain open.

Run `check-marker-prefix.sh` with the pinned iPRA and Foundation overlays used
by `check-increment-anywhere.sh`. The checker regenerates and rebuilds the
pinned dependencies in temporary storage and rejects `sorryAx` in printed
theorem dependencies. Set `TMPDIR=/dev/shm` if root-disk space is limited.
