# Why a typed zero-suffix objective does not enlarge the rotation search

## Claim

For a full binary source tree using the current `CI`, `CD`, `CB`, `CC`, and
`CH` semantics, suppose every source leaf is reachable from ordinal zero in
the abstract control-flow graph (both `CD` outcomes are retained). Then every
`CB`, `CC`, or `CH` leaf has an address ending in `1`. Consequently every leaf
whose address ends in six zeroes is a `CI` or `CD` leaf.

Both accepted source instances have this reachability property: K215 has
4,751 reachable leaves out of 4,751; ST215 has 4,732 out of 4,732. A rewrite
that preserves their entire guarded ordinal control-flow graph preserves
this property. Within that rewrite class, excluding six-zero suffixes only
at `CI`/`CD` leaves is exactly as restrictive as excluding them at all leaves.

## Proof

Suppose a non-fallthrough instruction (`CB`, `CC`, or `CH`) were the leaf at
address `p0`. Let `S` be the nonempty right sibling subtree at address `p1`.
No instruction outside `S` has an edge into `S`:

* A fallthrough edge into `S` could come only from its immediately preceding
  leaf, namely `p0`, which has no fallthrough edge.
* A forward cut targets the end of an ancestor subtree of the instruction
  taking the cut. The only subtree outside `S` with end equal to the start
  of `S` is the singleton leaf `p0`. A cut cannot select that singleton as
  its ancestor: selecting an ancestor requires an edge below it. Any other
  selected subtree either lies outside `S` or contains `S`, and its end is
  therefore outside the half-open ordinal interval of `S`.
* A backward cut targets the start of an ancestor subtree of its instruction.
  If its source is outside `S`, laminarity of binary-subtree intervals makes
  that start lie outside `S`. An ancestor containing `S` starts strictly
  before `S`, because `S` is a right child.
* A halt has no successor, and wraparound targets ordinal zero, which lies
  outside the right-child subtree `S`.

Thus `S` has no incoming edge from its complement. Ordinal zero is outside
`S`, so every leaf of `S` is unreachable. This contradicts the premise.

The argument also permits changing control depths while preserving the same
complete graph. It does not rule out introducing unreachable padding,
changing the abstract control-flow graph, or modifying the binary runtime.

## Search consequence

The typed searches in `typed_ST202` and `typed_ST203` were exploratory beam
searches, not exhaustive searches or lower-bound proofs. Their objective was
to count only `CI`/`CD` leaves ending in six zeroes, while retaining maximum
zero-run length at most six. The preceding lemma explains why this objective
does not produce a new feasible class under their exact-CFG rotation rules.

The executable `check_scanner_typed_obstruction.py` independently reconstructs
the interval control-flow graph from each source file and checks its full
reachability and literal terminal-symbol census. Its finite receipt supports
the instance premises; the general argument is the proof above.
