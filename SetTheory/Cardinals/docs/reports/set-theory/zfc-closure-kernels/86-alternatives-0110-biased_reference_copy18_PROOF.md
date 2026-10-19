# Exact 18-state variable-anchor copier quotient

Import the established 19-state copier in variable-anchor mode. Its states
`after_anchor` and `find_ones` have the following rows:

* On zero both preserve zero and move right to `find_first`.
* On one both preserve one and move right to themselves.

Identify the two states and retarget incoming transitions through that map.
For both symbols, their transitions have the same write, move, and projected
target. Thus this is an exact deterministic transition-system quotient on all
configurations, not merely on reachable prepared frames. The table generator
checks those two equalities before constructing the 18-state table.

Projection of the old control state, with identical tape and head, commutes
with each literal TM step. Induction on the execution length therefore
preserves the old copier's termination, output, runtime and head trajectory.
There are 17 operational states and one totalizing sink, with a separate
external RETURN port. The port remains an enclosing machine's obligation.

The prepared-frame theorem is inherited from the earlier biased copier.
Source r is stored as a run of r+3 ones with its first one erased. The left
counter initially consists of its single sentinel, and the counter gap is at
least r+2 cells. Output restores the source, loads 1^(r+1) into the counter,
and returns on its rightmost one, preserving every other tape cell.

The positive anchor run may be extended to any finite nonempty list of
positive one-runs separated by single zeros and ending in one zero. The left
shuttle still meets no adjacent zeros before the counter gap. The right
shuttle scans those runs with `find_ones` and `find_first`, so it still reaches
the source's unique two-zero marker before any other adjacent zeros. Induction
over the list of positive runs proves this extension. In particular all four
fixed seven-cell headers 1^k 0 1^(5-k) 0, 1<=k<=4, satisfy it.

The generator's 1,980 regressions cover variable single anchors and all four
seven-cell headers, varied source values and positions, minimum counter
capacity, and arbitrary exterior bits. They supplement the inherited
unbounded induction and the exact quotient argument. No proof-assistant
compilation or complete verifier/blank-bootstrap construction is claimed.
