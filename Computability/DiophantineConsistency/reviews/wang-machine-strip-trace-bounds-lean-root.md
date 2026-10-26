# Actual head containment and finite trace bounds

Date: 2026-10-26. ROOT read both complete main/check packets and author
receipts, inspected the proofs, and ran four fresh capped Lean commands.
This is independent review of the two agents' sources. The existing
dependency objects were reused; no complete closure rebuild is claimed.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942HeadBounds.lean (135 lines) | bed402c366871656a605ebef749451631c88b34ce57118fa6bea583fce700754 |
| WangTiles942HeadBoundsChecks.lean (74 lines) | 9787951e938a1b510d180b767e6359affbb9c460364bde2cd92f94b63742e538 |
| WangMachineTraceBounds.lean (142 lines) | 2a4c16552c74a33445f8aa5302d5ab108f327708a08f468c4e61e6afcd85e718 |
| WangMachineTraceBoundsChecks.lean (85 lines) | 22e106989ecf6d9958fc6b86c650797d489b4b2734ca076391c8b2dedcae944c |

`next_head_inside` uses actual allowedness, horizontal matching, the
persistent strip and an encoded operating configuration. Its exact
transition has an active rail at least6; the left wall's facing edge is
at most2 and the right wall's at most4. Matching excludes landing on
either wall, and the actual one-cell displacement gives strict bounds.
No time-matching, no-finish, successor-live or successor-row premise is
present. Entry into halt still moves and remains covered. The inactive
edge negative control prevents a false claim about both transition edges.

The trace bounds are generic for every actual `Machine n`, including
zero states, arbitrary initial head and unnormalized tape. After t steps
the head lies within t of its initial position. A tape read at either
inclusive extreme or farther away is unchanged: the final write occurs
before movement. From the blank initial tape this yields read=false
whenever |x|≥t. Independent margins L>T and R>T enclose the finite trace;
after a given halt time T the same bounds apply at every later time.
The tests exercise both halt-entry directions, stationary halt, t=0,
duplicate tape entries, unequal margins and the sharp support threshold.

All four root commands used `lake env lean -M6000 -j1`; both main outputs
went to separate `/tmp` objects, and checks imported the frozen author
objects. Both main logs are empty. HeadBounds has nine standard-only
axiom reports, check log SHA-256
`8502196034aec7f1dc7d1b7925191324039e5607ea450c07d11d7094c115afc0`.
TraceBounds has thirteen standard-only reports, check log SHA-256
`8ee40f2975e0b58986765951555a4ca573a4147c7b07c3df3fb232bf8c173122`.
Only subsets of `propext`, `Classical.choice`, and `Quot.sound` occur.

Author receipts: [head bounds](wang-tiles942-head-bounds-author.md) and
[trace bounds](wang-machine-trace-bounds-author.md). These establish
operational bounds, not a supplied row-step or cofinal tiling theorem.
The decimal equation page and its metrics are unchanged.
