# Bounded search for reuse of the new marker helper

This is an exploratory finite search, separate from the accepted CM215 proof.
It found no qualifying replacement and establishes no state lower bound.

The input is the accepted native CM215 table, SHA-256
`e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252`.
The search removes helper state 176 and changes only state 52 on symbol zero.
It tries all 214 surviving target states, both written symbols, and both move
directions: 856 replacement rows. Recursive visits to 52/0 use the proposed
replacement, so a helper that depends on the old row is not silently accepted.

The initial local tape has predecessor bit `m` at position -1 and zero at
position 0. All other cells are arbitrary. For each proposed row, symbolic
execution branches on each newly inspected outside cell. A successful block
must reach state 168 for `m=0`, or state 154 for `m=1`, with head at position 1
and every visited cell restored. Unvisited cells remain untouched. The first
row may temporarily change position 0; restoration is checked at the end.

Bounds per initial marker case are 96 transitions after the proposed first
row, ten visited cells, and 4,096 symbolic nodes. The marker-one case is checked
only if marker zero passes. Exceeding any bound is an unresolved search exit,
not a counterexample to unrestricted helper reuse. A separate positive sanity
check verifies that the existing helper176 realizes both required branches.

No replacement passed both cases. Of the 856 marker-zero attempts, 850 reached
the cell bound, two reached the transition bound, three halted or reached an
unavailable state, and one passed. Its marker-one case reached the cell bound.
The exact counts and search limits are in the JSON receipt.

Reproduce from this directory by providing the table and output paths:

```sh
python3 -B final_helper_reuse_search.py --table ../../machine/marker215.native.tm --output final_helper_reuse_search.json
```

The script does not modify any machine table. This search does not inspect
guarded source contexts or attempt a global reallocation. It adds no premise
to the accepted CM215 theorem.
