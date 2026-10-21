# Scanner-aware source research

This subtask did not construct a 214-state machine or a new accepted 215-state machine.
It produced two exact alternative source layouts, a source-only verification script,
and independent support for the root agent's window-invariant method.

## What the scanner actually detects

In native K215, the rows for states 2, 3, 5, 9, 15, 23, 34, and 50 form the
successive stages of an eight-zero recognizer. Each read-one row returns left
to state 2. The read-zero row of state 50 enters the rightward return scanner
75. Removing 50 and redirecting 34/0 to 75 recognizes seven zeros instead.

A six-zero terminal source address can temporarily produce a seven-zero run
because the engine shifts a zero immediately after the address. This occurs
in the pinned repository's already documented failing CD1 example at ordinal
26. The first return sees six terminal zeros and is harmless; a later return
sees seven, which is precisely where the shortened scanner loses the address.
The auxiliary `scanner_probe.py` is a trace diagnostic, not a general proof.

The 37 problematic source occurrences are retained in
`sixzero_occurrences.json`: 22 CD1, 11 CD2, two CD8, and two CI1 occurrences.
They are distributed through shared constructor blocks, so deleting one
logical axiom row does not automatically eliminate the obstruction.

For a complete finite binary source tree, forbidding every terminal suffix of
six or more zeros is equivalent to forbidding a run of six zeros anywhere
in any leaf address. Indeed, from any prefix ending in six zeros, extending
only by left edges reaches a leaf with a terminal suffix at least that long.
Thus a terminal-suffix objective exactly captures the usual maximum-zero-run
constraint for these full trees.

## Exact source results

`zero205/best-sites.json` has the same 4,751 ordered instructions and both
complete guarded control-flow graphs as primary K215, maximum zero run five,
and 205 distinct source subtrees. Its recipe contains 13 global rotations.
The initial 202-subtree source required a maximum zero run of six.

`zeroST204/best-sites.json` has the same 4,732 ordered instructions and both
complete guarded control-flow graphs as the incoming direct-transfer ST215
source, maximum zero run five, and 204 distinct source subtrees. Its recipe
contains 12 global rotations. The exact occurrence count should be taken
from its independently generated source-audit receipt if the inherited
source is updated.

The independent verifier `verify_scanner_sources.py` reconstructs each source
from its baseline and recorded rotations, compares the ordered instruction
word, and computes the guarded control-flow graph in two different ways:
ancestor intervals and literal binary address arithmetic. It imports no
search implementation. The audit receipts are under the two source folders.

The bounded beam searches examined 164,486 and 216,486 proposed rewrites,
respectively. They are incomplete heuristic searches, not minimality proofs.
The more permissive whole-source-CFG searches did not lower those two costs
within their recorded time bounds. The completed search receipts state their
actual scope and counts.

Neither source has been allocated into a complete binary table in this
subtask. In particular, a source-DAG count is not a physical state count,
and the anticipated scanner saving has no accepted runtime/startup proof
for these newly encoded layouts. The naive accounting of three extra source
subtrees against one deleted scanner state does not improve the baseline.
These files are concrete leads for joint allocation and source optimization,
not new small-machine candidates.

## Independent window audit

`audit_invariant.py` checks an explicit finite window family without running
the root worklist algorithm. It reconstructs each successor using lists of
bits and checks both possible new exterior bits. On the pinned primary K215
and `root_work/invariant5.json`, it verified 87,795 window configurations and
175,526 nonhalting successor obligations. The initial state contains all
2,048 radius-five windows, and all 31 reported conditional marker pairs pass
independent validation. This supplies an ordinary finite inductive-closure
check for arbitrary initial tapes from state 0, not a proof-assistant theorem.

## Comparison corpus

`corpus.py` examines the materialized repository and its six incoming ZIPs.
It found 399 complete, graph-reachable 215-state table files, containing 128
literal byte-distinct tables and 86 graph families up to arbitrary state
renaming and global tape reflection. The canonical representation respects
read symbols, written symbols, and transition directions. It is a structural
comparison, not a decision procedure for behavioral equivalence and not a
claim of novelty outside the pinned repository.
