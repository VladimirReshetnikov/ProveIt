# Cell-sum bounds for the marked base and pulsed words

`CompactMarkedCellSum.marked_cell_sums` proves, in every model of IΣ₁,
both `cell_sum` bounds for the actual base cell word
`X0 j = packedCell (row j) 0` and the perturbed word
`X0 j + 2^(67*1063) * δ j`. It assumes a `CompactWord row N s` and that
`δ j ≤ 1` for `j < N`. The compact word supplies `row j ≠ 1` for every
valid cell and `0 < N`; the latter ensures both cyclic indices used by each
transport block are also below `N`. The result needs neither definability of
the row or pulse functions nor a pulse-support restriction for this
pointwise size conclusion.

It applies the separate proved support size, single-pulse size and
`cell_sum_of_small` theorems to both words. It does not establish high-mask
disjointness, complete packing, a graph zero or an iPRA theorem. The kernel
is the exact symbolic `paramKernel rho`; retained-byte binding remains a
separate boundary.

The guarded author run, session `40580`, exited 0 without warnings or
`sorryAx`; the named theorem's Lean axiom report contains only `propext`,
`Classical.choice` and `Quot.sound`. The project overlay contained 524
distinct names, including 339 overlaps and 338 three-provider overlaps; all
overlapping hashes matched, and recorded provider and sampled direct-import
guards were unchanged. The runner, compiler/dependency observations and
per-file inventories are retained under `observations/attempt01`. This is
an incremental single-author check, not a paired replay or a fully
authenticated source/object closure; package, transitive and dynamic-loading
ancestry is inherited and `/tmp` paths are ephemeral.
