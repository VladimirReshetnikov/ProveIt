# Chosen calibrated rank for a constructed compact word

`CompactWordChosenRank.lean` proves that the zero-dummy cell word determined
by a supplied Σ₁-definable `CompactWord` can be used in the existing chosen
controller theorem. It derives the base word's `PackingInput` origin and
low-mask fields and single-pulse low-mask safety from the concrete cell,
rather than requiring those facts as separate assumptions. Under its remaining
explicit premises, Lean proves existence of a definable Boolean selector with
the prescribed nonwrapping support and a perturbed `PackingInput` whose
`windowRank` has the specified calibration residue.

The theorem **still assumes** the five shared scalar bounds (`N > 1`,
`s < N`, the low-mask bound and both high-mask bounds), plus all five
`TransportFields` for the base word: the kernel-product bound, cell-plus-block
bound, origin block positivity, and both high-mask no-carry fields. It also
assumes those same five `ProductBlockInput` fields for the perturbed word
**uniformly for every** definable Boolean selector satisfying the stated
positive and nonwrapping support conditions. The new independently checked
cell-product bound is not yet imported here, so this theorem still lists the
two `hi_lt` premises. No graph zero, retained-coefficient binding, complete
converse or iPRA proof follows without the remaining work.

The first attempt failed before elaboration because a targeted provider
overlay omitted a transitive controller object; its compiler log and receipt
are retained in `observations/attempt01`. The corrected bounded single-author
build, tool session `74468`, exited 0 without warnings or `sorryAx`, with
unchanged direct dependencies, complete selected union-overlay inventory and
selected packing-provider root inventory. Before the build all 338
overlapping files across the two provider roots had matching hashes. The
preflight, source/object hashes, command, log and terminal receipt are in
`observations/attempt02`; both named axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.

This is a mixed-provider author-side result, not a paired replay or a
complete independently authenticated closure. Package, transitive,
dynamic-loading and between-observation ancestry remain inherited.
