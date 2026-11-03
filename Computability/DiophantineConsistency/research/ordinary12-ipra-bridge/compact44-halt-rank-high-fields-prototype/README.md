# Halt-derived chosen rank with high-mask obligations remaining

`CompactHaltRankHighFields.lean` joins the model-halt chosen-rank theorem
with `CompactMarkedCellSum.marked_cell_sums`. The latter proves the
cell-plus-normalized-block bound for the actual base and Boolean-pulsed cell
families, so neither cell-sum field remains an assumption.

Under a model-internal halt, the theorem constructs a definable Boolean
selector with the stated positive and nonwrapping support, a pulsed
`PackingInput`, and the calibrated rank congruence, **assuming only the two
high-mask no-carry fields** for the base cell family and those same two
fields uniformly for every admissible definable Boolean perturbation. The
origin field uses `highNat - 1`; the non-origin field uses `highNat`. These
are substantive, unproved assumptions in this theorem. It does not prove a
graph zero, retained-byte binding, a full converse or an internal iPRA proof.

The bounded single-author build, tool session `12118`, exited 0 without
warnings or `sorryAx`. Its axiom report lists only `propext`,
`Classical.choice`, and `Quot.sound`. Direct dependency guards, the complete
selected project overlay and selected controller, symbolic-kernel and
static-mask root inventories were unchanged. The full provider overlap
comparisons, selected inventories, source/object hashes, command, dependency
listing, log and terminal receipt are retained in `observations/attempt01`.

This is a mixed-provider author-side result, not a paired replay or a
complete independently authenticated closure. Package, transitive,
dynamic-loading and between-observation ancestry remain inherited.
