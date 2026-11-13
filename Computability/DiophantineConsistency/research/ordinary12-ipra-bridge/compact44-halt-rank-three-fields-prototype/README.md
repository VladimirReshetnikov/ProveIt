# Halt-derived chosen rank with three remaining block fields

`CompactHaltRankThreeFields.lean` joins the previous model-halt chosen-rank
theorem with the compact-word block positivity theorem. The base and pulsed
origin blocks are positive because each includes a positive cyclic
predecessor cell, so the two `blk_pos` premises are no longer assumed.

The theorem retains the model-internal halt premise, the cell-plus-block
bound, and the origin and non-origin high-mask no-carry fields for the base
cell family. It also assumes those **three** fields uniformly for every
definable Boolean perturbation satisfying the stated positive and
nonwrapping support conditions. Under these explicit physical premises, the
conclusion is the chosen definable selector, a pulsed `PackingInput`, and
the prescribed rank congruence. The theorem does not prove the remaining
fields, a graph zero, retained-byte binding, a full converse, or an internal
iPRA theorem.

The bounded single-author build, tool session `21340`, exited 0 without
warnings or `sorryAx`; its axiom report lists only `propext`,
`Classical.choice`, and `Quot.sound`. Direct dependencies, the entire selected
project overlay, and selected controller, symbolic-kernel and static-mask
root inventories were unchanged. The full provider overlap comparisons,
selected inventories, source/object hashes, command, dependency list, log and
terminal receipt are retained in `observations/attempt01`.

This is a mixed-provider author-side build, not a paired replay or a complete
independently authenticated closure. The package, transitive,
dynamic-loading and between-observation ancestry remain inherited.
