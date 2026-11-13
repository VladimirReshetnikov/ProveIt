# High-mask phase zero for every compact block

`CompactWordPhaseZeroHigh.lean` proves no-carry at local phase zero between
the actual normalized block and the exact symbolic high-mask digit, which is
4. It applies to a supplied `CompactWord row N s` and normalized dummy
cells at **any** model index `j`; no pulse definability, Boolean-dummy,
stride, high-mask or complete-packing premise is needed.

The proof strengthens the earlier kernel divisibility fact to `8 ∣ K` and
uses the exact kernel split to show the low and high product halves are
divisible by 8. The temporal predecessor cell is congruent to zero or one
modulo 8 because its first radix digit is a Boolean selector. Consequently
the whole block has residue **at most one** modulo 8, which is disjoint from
the high-mask bit 4. The result does not claim the residue is always zero:
for example, the temporal predecessor can be the marker row. It does not by
itself prove any other high-mask phase, a graph zero or an iPRA theorem.

The first bounded attempt failed on the model arithmetic proof of
`4 % 2 = 0`; its exact source and compiler output are in
`observations/attempt01`. The corrected single-author run, tool session
`22503`, exited 0 without warnings or `sorryAx`. The named axiom report lists
only `propext`, `Classical.choice`, and `Quot.sound`; direct dependency
guards, the full selected project union overlay and selected controller,
symbolic-kernel and static-mask root inventories were unchanged. Full
overlap comparisons, selected inventories, command, source/object hashes,
dependency listing, log and receipt are in `observations/attempt02`.

This is a mixed-provider author-side build, not a paired replay or a fully
authenticated dependency closure. Package, transitive, dynamic-loading and
between-observation ancestry remain inherited.
