# Local marker and return lemmas

These ordinary finite-transition arguments concern the exact table in
[relay217.native.tm](relay217.native.tm). They do not prove its global runtime
or its consistency calibration. The generic runtime attempt actually failed.

## Three-step marker relay

The accepted table has `36/0 = 0 R 51`. The proposed table replaces it by
`36/0 = 1 R 16`, changes `16/1 = 1 L 56`, and retains `56/1 = 0 R 51`.
Start at head `h` in state 36, reading zero, and suppose cell `h+1` is one.
The replacement writes a temporary one at `h`, preserves the one at `h+1`,
then clears the temporary marker. After exactly three steps it is in state 51
at `h+1`, with precisely the original entire tape. That is the accepted
one-step endpoint. All other cells are arbitrary. This argument assumes the
neighbor is one; it does not cover the first blank-bootstrap visit, where it
is zero.

## Six decoder returns can avoid changed state 16

The six rows with source states `42,47,57,126,139,141`, reading one, write zero
and move left into old state 16. Old `16/1` and retained `122/1` are both
`0 L 1`. Their zero rows differ. The proposed table redirects only those six
one rows to state 122.

For runs starting in state 0 or 84, every such return reads one in its new
head cell. This follows from predecessor writes, not a register-value sample:

| Caller | All incoming rows to that caller |
| --- | --- |
| 47 | `31/1 = 1 R 47` |
| 57 | `43/1 = 1 R 57`, `81/1 = 1 R 57` |
| 126 | `107/1 = 1 R 126` |
| 139 | `125/1 = 1 R 139` |
| 141 | `128/1 = 1 R 141` |

Each writes one immediately to the left of the caller. The caller writes
its own cell, then returns to that preserved one.

State 42 has incoming `28/1 = 1 R 42`, `109/1 = 1 R 42`, and
`83/1 = 0 L 42`. The first two have the same argument. For the last:

1. State 83 has only incoming `73/1 = 1 R 83`.
2. State 73 has incoming `123/1 = 1 R 73` or `62/1 = 1 L 73`.
3. In the first case the one written by state 123 is exactly the cell that
   the later return to 16 reads.
4. In the second case, state 62 was reached from one of
   `46/1`, `59/0`, `109/0`, `124/0`, `125/0`, all moving right. The last four
   write zero, contradicting the subsequent `73/1` read. Thus the predecessor
   is `46/1 = 1 R 62`.
5. State 46 has only incoming `30/1 = 1 R 46`. This writes one two cells left
   of state 62. The ensuing `62 → 73 → 83 → 42 → 16` path reads that one;
   none of its intervening writes changes it.

The named states are not either initial state. Backtracking the finite
predecessor chain is therefore justified; it cannot stop at an initial
configuration halfway through the argument. These rows are unchanged by the
proposal except the final targets. Every redirected two-step return has
exactly the old complete-tape endpoint.

A separate prefix census of all 4,744 source occurrences found 1,311 such
calls, all with next read one. It stops before unknown register data and is
only corroborating evidence. The predecessor proof above supplies the
arbitrary-tape local argument.

## The omitted route

State 16 also has incoming `10/0 = 0 L 16`. State 10 can be entered from
`6/1 = 0 R 10`, its own one loop, or `108/1 = 0 L 10`. The first two write
zero in the future state-16 cell. The third need not do so. The six-return
argument does not cover this route. The runtime failure at source ordinal
4569 remains outside the proved local lemmas. No equivalence of the whole
217-state proposal with accepted K218 is asserted.
