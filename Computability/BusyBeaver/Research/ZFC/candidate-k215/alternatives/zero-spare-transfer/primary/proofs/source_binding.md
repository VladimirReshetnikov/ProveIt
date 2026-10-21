# Exact transfer source and append-zero physical binding

## Unchanged language, explicit reconstruction

The selected source is the 201-node transfer DAG with 4,775 unfolded primitive
occurrences, SHA-256
05e7caa159d95cdf9ee254d313c44c52369ac91e52cbc23d54b15f0b64b95922.
It is byte-identical to the previously calibrated append-one transfer source.
The experiment changes physical spare allocation and blank startup, not its
commands, numerical axiom families or proof compiler.

For a dependency-closed reconstruction, the checker starts from the included
202-node baseline. It saves the old NIP at tree path 111 and old DROP at
110101. It replaces the old 1101 selector by (old 11010010, CB 1), then
replaces 111 by ((old DROP, old NIP), old NIP). The resulting flattened tree
must match the shipped source byte-for-byte. The four transported closed
bodies are old/new paths 11010010/11010, 110101/11100, 111/11101 and 111/1111.

For every transported body, verify.py compares every primitive and all
control edges in local ordinal coordinates. Every edge is either internal
or the single normal exit. This is stronger than comparing subtree hashes:
nonlocal break/continue rebinding would fail the explicit edge comparison.
The full structured CFG is calculated both by recursive break/continue
stacks and by source-prefix intervals. Both old and new calculations agree.
The selector dispatch is checked at source ordinals 23 and 24, while ordinal
4696 returns to the scheduler root. The composed command therefore has the
closed arithmetic meaning proved in composite_transfer_review.md, with the
same command fields and the same strong compiler.

All leaf paths form a complete binary tree, with no duplicate or prefix
leaves. The maximum depth is 44, within the 64-bit control region. Operations,
register indices, and branch-depth arguments are checked before simulation.

## Physical successor binding

For every source occurrence and both guards of each CD, the checker derives
the binary-prefix successor used by the runtime kernel and resolves it to
the first leaf of the appropriate subtree. Extra trailing zero padding may
be removed only while resolving an address beyond an existing prefix.
The resulting ordinal must equal the independent structured CFG edge.
The full 6,209-row binding census is included and regenerated on replay.

Physical registers encode the same logical registers under the pinned PHY
permutation (6,2,0,4,3,7,8,5,1). The dispatch marker, complete unary register
file, arbitrary nonempty finite spare suffix and both zero exteriors are
represented, not cropped. CI changes its chosen logical value by one and
appends spare value zero. It does not alter logical stack semantics.

## Exact table and canonical map

The included row recipe reconstructs the old append-one transfer215 table
from the inert baseline. Changing only native row (198,0) from (1,L,40) to
(0,L,40) produces the current rows. Its blank-start directive is 74. Native
halt is 254; there are 215 distinct working states and exactly 430 rows,
with every working state graph-reachable from 74.

The canonical bijection assigns native 74 to 0, assigns the other working
states to 1 through 214 in increasing native order, and assigns halt 254 to
215. The two shipped canonical maps must agree with the reconstructed map,
and every canonical row must be its image. Exact file hashes and start
labels are checked. No graph reachability check is treated as source or
blank-start correctness.

The symbolic kernel is retained unchanged from its owned predecessor. Four
one-block schemas are freshly derived from this table. Their literal and
unary trace rows are included explicitly in coverage, together with every
case's direct rows. All 430 rows must be covered, and each recorded schema
row must be an actual table row. The twelve schema rows are already among
the direct case rows for this source. The full append-zero run has 6,209
cases and 1,611,489 symbolic rules; its census digest is checked exactly.

## Startup, calibration and limits

Three implementations agree through all 73,172 blank transitions, and their
complete final support equals the whole encoded ordinal-119 frame, including
all 65 spares and the zero exterior. The exact 177-step source prefix from
AX entry ordinal 25 matches the entire logical store and program counter.
zero_spare_startup.md then uses the inherited terminating all-natural AX
contract to finish that partial command, counts eight safe heads and treats
171 as opaque. The independent review confirms d(0)=3 and permanent margin
five, while retaining the arbitrary-stack compiler's cofinal completeness.

The 4000-step symbolic construction bound is not a bound on actual unary
lengths, tape extent, spare-list size or runtime. The symbolic proof rules
use ordinary induction over natural unary lengths and finite block lists;
the source arithmetic, compiler and credit arguments remain separate
mathematical inductions. All inherited calculus/macro assumptions and
notices are identified in provenance/. The package is not a new formal
proof-assistant endpoint, an absolute consistency proof or a state lower
bound.
