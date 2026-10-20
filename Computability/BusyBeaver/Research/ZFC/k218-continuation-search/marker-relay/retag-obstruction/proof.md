# Why the remaining guarded CC2 loops cannot be retagged to CC3

This is an ordinary structural obstruction for **order-preserving binary-tree reassociation with the exact ordinal CFG**, not an allocation or runtime impossibility theorem. The input is the accepted primary218 source. The first relay failure is at ordinal4569, whose required successor is4567.

## Counting right-child crossings

A `CC k` returns to the beginning of the ancestor reached at its kth right-child crossing. Along the path from that ancestor to the continue leaf, every right-child crossing has a nonempty left sibling. Those left sibling leaf intervals are pairwise disjoint and occur between the target ordinal r and the continue ordinal i. Consequently

`k ≤ i − r`.

If a contiguous block in that interval is forced to remain a subtree by other CFG edges, a left-sibling partition cannot split that block: ordered-tree intervals are nested or disjoint. Collapse each such block to one atom to obtain the corresponding stronger bound.

Ordinal4569 returns to4567, so `k≤2` in every ordered tree realizing the same ordinal edge. It cannot become `CC3`, irrespective of changes to ancestors outside the fragment. The same distance-two argument applies to ordinals8,4587,4601 and4710.

The local guarded shape at4567 is moreover forced:

`A = (CD5, ((CD6,CC2),CB1))`.

The zero edge of `CD5` must skip to4571. Since the continue loop returns to4567, there must be an ancestor starting at4567 containing the continue. Its first leaf is this decrement; the nearest left-child boundary it can exit must end at4571. The zero edge of `CD6` at4568 skips to4570, forcing the pair `(CD6,CC2)`. Neither the zero branch nor the continued loop can be treated as a normal-returning fragment.

## The other cleanup loops

At ordinal4575 the target is4572, three leaves earlier. The intervening leaves are `CD5,CC1,CD6`. The first decrement's zero edge goes to4574, and `CC1` returns to4572. Together these force the two-leaf subtree `Z=(CD5,CC1)`; splitting it by reassociation changes one of these CFG edges. Thus only the two blocks `Z` and `CD6` precede the final continue along a right-sibling partition. Again `k≤2`.

The same argument applies to4575,4593,4607 and4716. The independent literal census in `review.py` records all nine occurrences of `(CD6,CC2)`, both decrement targets, and each continue target. It checks data; this counting/forced-block argument is the all-tree mathematical justification.

A reassociation such as

`(Z,((CD6,CC2),CB1))  ↔  ((Z,(CD6,CC2)),CB1)`

can preserve a cleanup loop's ordinal edges while retaining `CC2`. It still contains the forced `(CD6,CC2)` subtree and does not solve the distance-two failure at4569. No physical routing improvement is inferred from that syntax.

## Relation to Source141

Source141 retags `((X,X),CC2)` to `(X,(X,CC3))` with `X=(CI1,CI1)`. Both X blocks return normally. Each fragment adds four to register1 and exits with `continue1`; the extra right boundary is exactly compensated by the larger continue argument. The complete source checks preserve both decrement guards because there are no decrements inside this selected fragment.

The remaining relay failure is not an instance of that pattern: its short backward edge and guarded decrement pair force the above bound. Therefore this particular **CC2-to-CC3 reassociation route is blocked**. A genuine primitive-word change, another proved all-natural comparison routine, or a physical repair/reallocation remains a different task. This note asserts no new table, state count, startup or global runtime result.
