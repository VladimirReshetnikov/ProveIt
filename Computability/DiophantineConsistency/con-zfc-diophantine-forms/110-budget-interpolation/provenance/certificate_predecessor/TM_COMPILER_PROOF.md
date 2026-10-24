# A literal finite-tile compiler for deterministic binary machines

## Result and calibration boundary

The supplied `tm_tiles.py` constructs a literal finite tile set from any total deterministic binary one-tape machine with s nonhalting states, a specified nonhalting start state, left/right moves, blank symbol 0, and one designated halting target. Its strict-boundary rectangles exist **if and only if** the machine halts on a bi-infinite blank tape.

The compiler is generic and does not use Jones' universal expression. The concrete instantiation provided here uses the already pinned K215 table only to obtain a closed, previously calibrated example. The six-coordinate arithmetic theorem itself is independent of that choice. A separate direct-ZFC-checker-to-tile instantiation is not claimed.

The literal K215 output has 7,782 tiles and 2,162 nonzero colors. This removes the uninstantiated finite-tile-set gap for the K215 example. It does not remove the ordinary power-graph compilation or internal-arithmetic interpretation gaps. In particular, neither six nor nine is a final ordinary-polynomial variable count.

## Machine convention

A machine configuration consists of a state q, an integer head position p, and a binary tape with finite support. A transition delta(q,a)=(b,d,q') writes b, moves one position in direction d in {L,R}, and enters q'. Reaching the designated halting target stops, after that write and move. The supplied table has states 0,...,214, start 0, and halt target 215. Its sole halting-target transition is `68 1 1 R 215`.

The source SHA-256 is fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090. The source table, inherited notice and ordinary calibration exposition are retained in `upstream/`. References inside that inherited exposition describe the prior project provenance, not additional newly reproduced verification.

## Alphabet and local update

A cell symbol is either a plain tape bit p_a or a headed symbol h_(q,a), where q is nonhalting or the halt target. A legitimate finite configuration word has exactly one headed symbol.

For every triple (l,c,r) with at most one nonhalting head, define the radius-one output f(l,c,r):

- If c=h_(q,a), output the plain bit written by delta(q,a).
- If c=p_a and l has a head whose transition moves right into c, output h_(q',a), where q' is that transition's next state.
- If c=p_a and r has a head whose transition moves left into c, output h_(q',a).
- Otherwise output c.

No triple containing a halted head is included as a step triple. The cases are disjoint because the triple has at most one head. On a whole legitimate configuration, these local outputs are exactly one ordinary machine transition. A window boundary is supplied with a virtual outside plain blank bit. A step variant is omitted when its central head would move out through that boundary.

## The three row languages

All nonzero colors are typed, so colors from different roles cannot accidentally match.

1. Initial-row tiles have north edge 0 and south edge equal to a typed cell symbol. Their horizontal phase automaton recognizes precisely p_0* h_(q_start,0) p_0*: phase 0 permits blank cells before the head, the head changes phase 0 to phase 1, and phase 1 permits blank cells afterward. A left-boundary variant is permitted only with incoming phase 0; a right-boundary variant only with outgoing phase 1. Both boundary edges may be zero on the head tile, so width one is represented correctly.

2. Step-row tiles for (l,c,r) have north edge cell(c), south edge cell(f(l,c,r)), west edge the typed pair (l,c), and east edge the typed pair (c,r). A left-boundary variant replaces its west edge by 0 only when l is the virtual plain blank and no head escapes left. A right-boundary variant analogously requires r to be virtual blank and no head escapes right. Opposite boundary variants may coexist if both requirements hold.

3. Halt-row tiles have south edge 0 and north edge a typed cell symbol. Their separate horizontal phase automaton recognizes precisely plain* h_(halt,a) plain*, with any plain bits and exactly one halted head. The same incoming/outgoing phase restrictions define the side boundary variants.

The initial and halt horizontal colors, step overlap colors, and vertical cell colors are all distinct nonzero colors. They are assigned consecutive integer labels by a deterministic ordering. Color 0 is used only for boundary variants.

## Soundness: every finite rectangle gives a halting run

Take any strict-boundary tiling of any finite positive width and height.

Only initial tiles have north color 0, so the top row consists entirely of initial tiles. Horizontal phase matching and the strict side boundaries force its south cell word to be blank except for exactly one start-state head. Only halt tiles have south color 0, so the bottom row consists entirely of halt tiles and its north word has exactly one halted head. No tile has both north and south color 0, so a one-row rectangle is impossible.

Every intervening row consists entirely of step tiles: initial tiles would illegally expose north zero, and halt tiles would illegally expose south zero. At adjacent interior cells, the overlapping pair colors imply that their three-symbol windows overlap consistently. Vertical matching identifies every window's center with the cell symbol from the row above. The side variants fix the two missing outside neighbors to plain blank.

Induct on the step rows. The first input word is a legitimate one-head configuration. The local update lemma makes the output word exactly its machine successor. The explicit boundary omission prevents the head from leaving the window, and outside cells remain untouched blank cells. Consequently each row is the restriction of the actual bi-infinite-tape computation, up to an irrelevant translation of the initial head position. The final word is halted because the bottom phase automaton accepts exactly one halted head. Hence the actual blank computation halts.

This argument covers arbitrary rectangle widths and heights, not only the bounded fixtures checked by the program.

## Completeness: every finite halting run gives a rectangle

Suppose the machine halts after T transitions. A finite run visits only finitely many tape positions. Choose a finite interval containing all visited positions, including the final head position, with at least one extra blank cell on each side.

Use the initial phase row to emit the initial blank configuration with its unique start head. For each transition, use the step tile whose triple is the actual old neighboring cells and whose south symbol is the actual new cell. Unique-head configurations satisfy the at-most-one-head triple restriction. The chosen padding makes all boundary neighbors blank and prevents boundary escape. Close with the halted phase row.

All adjacent colors match, and exactly the exterior edges have color 0. The resulting rectangle has height T+2. This proves completeness for every finite halting run, with no upper bound on T or the interval width.

## Exact tile and color counts

There are eight initial-row variants and sixteen halt-row variants. For the step rows:

- All-plain triples contribute eighteen boundary-aware variants.
- Each of the 2s headed symbols contributes six variants with the head at the left position, six at the center, and six at the right position. At the center, the outward-moving boundary is forbidden, but the opposite boundary remains available.

Thus the total tile count is

    k = 18 + 36s + 8 + 16 = 36s+42.

The vertical alphabet has 2+2s+2=2s+4 colors, including headed halt symbols. The step overlap alphabet has four plain/plain pairs plus 8s headed/plain or plain/headed pairs. The phase automata contribute four additional colors. Thus there are exactly

    (2s+4)+(8s+4)+4 = 10s+12

nonzero colors. The typed construction makes these classes disjoint. Within each class, the local fields determine the tile, so deduplication removes no count claimed here.

For s=215 this gives k=7,782 and 2,162 nonzero colors. The arithmetic certificate can choose

    C=8192, A0=134217728, D=35184372088832.

The packed binomial arguments have degree at most 373,533 and 350,190. Conditional graph counts remain 6+2p+b or 9+5p. These counts do not hide the missing p and b.

## Relation to consistency

The inherited pinned K215 ordinary calibration states that its blank halting is equivalent to syntactic inconsistency of ZFC. Combining that inherited equivalence, the generic compiler theorem proved above, and the global packed-convolution theorem gives an explicit exponential/binomial certificate for inconsistency, and a power-only one as well.

This new work establishes the machine-to-tiles and tiles-to-special-function certificates by ordinary mathematics and executable artifact checks. It does not independently re-prove all upstream K215 calibration, does not supply an ordinary graph polynomial for variable exponentiation, and does not supply the full object-language arithmetic interpretation. Consequently it does not yet claim a new completed ordinary Diophantine polynomial for Con(ZFC).

## Executable evidence

`check_tiles.py` regenerates the literal K215 tile table and verifies its source pin and exact counts. It independently checks all 7,758 step variants by an imperative five-cell machine update. It enumerates all 64 complete one-state binary machines and compares direct bounded machine execution against a separate literal-edge tiling-row search for 1,600 width/time combinations. Thirty-two halting machines produce complete positive rectangle witnesses. Both normal and Python optimized runs pass. These tests support the universal theorem above; they do not prove nonhalting or consistency.

## Square-tableau corollary: one more exposed coordinate disappears

For this compiled blank-start machine language, rectangle existence is equivalent to square existence. Suppose the machine halts after T transitions. There are T+1 head positions, consecutive ones differing by one, so the interval from the least visited position to the greatest has length at most T+1. Every written tape cell belongs to that interval because the tape starts blank.

Take the left endpoint to be the least visited position and extend the interval rightward to exactly T+2 cells. Every actual configuration is supported inside this interval. There is no need to have an unused blank cell on both sides: the step boundary rule only forbids an actual transition out of the interval, and every successor head position is one of the positions used to define the interval. Outside cells remain blank. Thus the same complete history occupies a strict-boundary square of width and height T+2. Conversely a square is a rectangle, so soundness already applies.

Consequently the compiled-machine instance may identify the dimensions by setting b=a in the global arithmetic certificate. The independent generic-rectangle theorem still uses six exposed coordinates; this machine corollary uses exactly five, a,Q,G,Z,r:

    Q=C^(a+1),    1+(C-1)G=Q^(a+1),    binom(A,Y)=2r+1.

Its conditional natural-polynomial count is **5+2p+b**. Replacing r by the four parity-extraction coordinates gives the power-only count **8+5p** with exactly five power graph calls. Eight is an exposed-coordinate count, not a final ordinary-polynomial count.

The square construction is checked for all 32 halting one-state fixtures and for 60 longer halting chains of lengths 1 through 20, with leftward, rightward and alternating motion. The straight-motion cases have the extremal visited span T+1, so these checks exercise the reason symmetric one-cell padding would be unnecessarily large.
