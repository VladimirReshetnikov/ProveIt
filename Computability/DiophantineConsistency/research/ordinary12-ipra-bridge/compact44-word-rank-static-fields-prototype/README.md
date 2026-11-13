# Chosen rank at the exact compact dimensions and masks

`CompactWordRankStaticFields.lean` specializes the prior four-fields theorem
to the chosen dimensions and the native symbolic `lowNat` and `highNat`
masks. It derives the two dimension inequalities from
`CompactPackingGeometry.geometry` and the three mask inequalities from
`CompactSymbolicMaskFields.masks`, using the checked equality between
`lowNat` and `CompactConcreteIncrement.mask`. The five scalar hypotheses
of the preceding theorem are therefore no longer assumptions here.

For a supplied Σ₁-definable `CompactWord`, the theorem still assumes the
cell-plus-block bound, origin block positivity, and both high-mask no-carry
fields for the base cell family. It also assumes **those same four fields
uniformly for every** definable Boolean selector with the stated positive,
nonwrapping support, applied to the corresponding pulsed cell family. Under
those explicit physical premises, Lean produces a chosen selector, its full
pulsed `PackingInput`, and the calibrated `windowRank` congruence. It does
not prove those block fields, a graph zero, retained-byte binding, an
end-to-end converse, or an internal iPRA proof.

The bounded single-author build, tool session `10065`, exited 0 without
warnings or `sorryAx`; its axiom report lists only `propext`,
`Classical.choice`, and `Quot.sound`. Direct dependencies, the complete
selected word/controller overlay, controller root, symbolic-kernel roots, and
static-mask root inventories were unchanged. Before compilation the runner
compared all 338 word/controller overlaps, 339 radix/overlay overlaps, 346
static/overlay overlaps and 11 static/controller root overlaps, with no hash
conflicts. The full comparisons, selected inventories, command, source and
object hashes, dependency list, log and terminal receipt are retained in
`observations/attempt01`.

This is a mixed-provider author-side build, not a paired replay or a complete
independently authenticated dependency closure. Package, transitive,
dynamic-loading and between-observation ancestry remain inherited.
