# Packing assembly with the remaining product and high-mask fields explicit

`CompactWordPackingFields.lean` joins the checked origin and low-mask
results to the full `PackingInput` interface for both the base and pulsed
cell families of a supplied `CompactWord`. The perturbation is still assumed
Boolean and supported away from the origin. For both word families, the
theorem explicitly assumes the following unresolved fields:

* the per-cell kernel-product bound;
* the cell-plus-normalized-block bound;
* positivity of the origin block;
* the origin high-mask no-carry fact;
* the non-origin high-mask no-carry facts.

It also assumes five shared scalar conditions: `1 < N`, `s < N`, the
concrete low-mask bound, positivity of `HP`, and the upper bound on `HP`.
Thus the result **does not prove those premises**, establish a graph zero,
or produce an internal iPRA proof. It packages precisely which facts remain
to be supplied when constructing the two `PackingInput` witnesses needed by
the rank-variation argument. `pulsedCell` is defined by the same displayed
pointwise formula as the canonical perturbation; a later client must still
connect any other named presentation it uses.

The first attempt stopped at its dependency guard because the historical word
provider does not contain `ArithmeticPacking.olean`; no Lean compile ran.
The corrected run used a dedicated overlay of all word-provider
`DiophantineConsistency` files plus the missing packing object. Before the
run, all **338 overlapping files across the complete word and packing
providers** had equal SHA-256 hashes; every selected overlay slot and its
resolved target were recorded and unchanged after compilation. The complete
overlap comparison and overlay inventory are in
`observations/attempt02/overlay-preflight.json`.

The bounded single-author build, tool session `47664`, exited 0 without
warnings or `sorryAx`. Its axiom report lists only `propext`,
`Classical.choice`, and `Quot.sound`; the command, source/object hashes,
direct dependency guards, compiler log and terminal receipt are retained in
`observations/attempt02`. This is a mixed-provider exploratory build. The
word and packing providers' package, transitive and dynamic-loading ancestry,
and between-observation limitations, remain inherited; the result is not a
paired replay or independently authenticated full dependency closure.
