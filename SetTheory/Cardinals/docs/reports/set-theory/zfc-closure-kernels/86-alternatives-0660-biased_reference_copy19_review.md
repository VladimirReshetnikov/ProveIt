# Independent review: 19-state copier quotient and variable anchor

Date: 2026-10-18. Source: `../native_copier/biased_reference_copy19.py`.
Hashes are recorded in `biased_reference_copy19_independent_audit.json`.

## Verdict

Both 19-state tables preserve the 21-state biased copier's exact valid-frame
contract. The fixed-anchor table uses anchor `10`. The optional table permits
any finite positive anchor `1^a 0`, a>=1, without increasing the state count.
Both have 18 operational states plus one reject state, 38 rows, and separate
return 19. The two additional state eliminations are rigorously justified by
complementary forced read symbols, not just agreement on finite test cases.

## Exact restricted quotient

Let f identify `erase_first` with `return_left` and `erase_second` with
`add_loop`, and otherwise retain and renumber every state (including the
separate return). The constructed quotient copies the retained state's old
zero row and the removed state's old one row. Redirect every incoming target
through f.

There are exactly four old state/read pairs for which a global conjugacy is
not claimed:

- (`erase_first`,0), (`erase_second`,0);
- (`return_left`,1), (`add_loop`,1).

All other old rows satisfy the literal one-step identity: if an old row reads
b, writes w, moves d, and targets q', the new row at f(q),b writes the same w,
moves the same d, and targets f(q'). The independent checker verifies this
identity over the entire finite old table outside those four exclusions.

The universal biased-copier invariant excludes all four pairs. At initialization,
source fields encode r by r+3 ones, so the first two cells after the restored
source start are both one when `erase_first` and `erase_second` read them.
At `add_loop`, the head is on the first zero after the current counter, and
capacity g>=r+2 ensures that zero exists before every increment. At
`return_left`, the head is again on the first remaining gap zero; there are
at least two at completion. Thus `add_loop` and `return_left` always read zero.

Induction on literal execution steps now gives identical tapes, identical
heads and projected control states throughout every valid run. The original
21-state run terminates by the previously reviewed moving-marker induction,
so the quotient terminates at exactly the same step count and head position.
Conversely every quotient step from that initialized run is the projected old
step; no additional rejection or halting event appears. The full-tape theorem
therefore transfers without a new macro proof. This is a reachable-domain
quotient, not an equivalence on arbitrary malformed tape configurations.

## Arbitrary positive anchor

Before quotienting, replace the old `after_anchor`/one rejection row by
`(write 1, move R, stay after_anchor)`. Keep its zero row unchanged. On a
positive anchor of length a, `gap_right` consumes the first anchor one, the
new loop consumes exactly a-1 further ones, and the unchanged zero transition
passes the unique following delimiter. All these cells are preserved.

The backward scan already handles an arbitrary nonempty block of anchor ones:
it crosses the isolated zero delimiter to its right and scans left through
those ones, then recognizes the two or more counter-gap zeros. Therefore the
same source-marker/counter induction applies for every finite a>=1. No new
counter capacity is consumed by a longer anchor and no extra blank cell is
required. All four forced-read exclusions remain valid, so the identical
quotient proof transfers this generalized contract to the variable-anchor
19-state table. Anchor length zero or an unbounded missing delimiter is not
covered.

## Independent executable evidence and integration boundary

`audit_biased_reference_copy19.py` checks both emitted table byte parsings,
all nonexcluded old transition identities, and 480 independently prepared
whole-tape runs with exact step-by-step control projection: 96 unit-anchor
runs and 384 variable-anchor runs. These include r=0,1,2,3,9,25, minimum gap,
multiple preceding fields, nonblank adjacent exterior cells, translated origins,
and anchor lengths 1,2,7,19. All 18 operational quotient states are exercised;
no excluded old read occurs. Maximum tested length is 3,396 steps. The finite
checks supplement the universal arguments above.

Table hashes:

- Unit anchor: `65483b9f128e91e2b4ea80f2c6dc3bf4a9f58b9e7e74694681bfcc8a0fdb14af`.
- Variable anchor: `efc47fd59e40cf3b0f85b862d2a7b550768b768937a2b1803f3c795545c21c82`.

A larger traversal may share the reject sink, making this copier's operational
contribution 18 states, but it must still charge the common sink, entry/head
adapters, destination reset, source-marker preparation and all search logic.
The restored marker and biased field interpretation remain as reviewed for
the 21-state component. The variable anchor can carry another positive unary
quantity only if the caller preserves its delimiter and proves all other
component interfaces accept the chosen anchor representation.

No producer file or shared source was modified by this review.
