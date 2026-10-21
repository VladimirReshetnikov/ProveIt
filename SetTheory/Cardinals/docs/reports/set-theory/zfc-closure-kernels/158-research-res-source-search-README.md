# Source reassociation and exact row alternatives

These are bounded discovery programs. They do not establish a 217-state
consistency construction or a lower bound. The exact recorded scopes are
in `result.json` and the two full text logs.

## Reassociation beams

From this directory, with a C++17 compiler:

```sh
g++ -O3 -std=c++17 dag_beam.cpp -o /tmp/zfc-dag-beam
/tmp/zfc-dag-beam k218.dag /tmp/zfc-baseline-result 300 218205
g++ -O3 -std=c++17 dag_dual_beam.cpp -o /tmp/zfc-dual-beam
/tmp/zfc-dual-beam dual-rho6.dag /tmp/zfc-dual-result 300 218205
```

The time limit is checked at iteration boundaries, so elapsed time can
slightly exceed it. Proposal counts vary with CPU speed. The recorded runs
reached 252 and 113 rounds, respectively. The input seed and beam policies
are fixed; the historical counts are in the logs. The interning pool is
compacted periodically, resetting the seen-root IDs; counts therefore must
not be described as globally distinct sources.

Each DAG begins with `node_count root_id`. Subsequent lines are nodes in
topological order. An internal node contains two nonnegative child IDs;
a primitive has a negative first field: -1 = CI, -2 = CD, -3 = BR,
-4 = CO, with the second field its parameter. The same subtree is shared
at all its occurrences. The rotation conditions are outward break(A)=0
and outward continue(C)=0 for `((A,B),C) <-> (A,(B,C))`.

The baseline input is the pinned 205-node source. The dual input is the
206-node, zero-run-seven source from the classical dual-rho6 experiment
in `../formalism/dual-rho6-price/candidate156534/`.
The selected zero-run-six and zero-run-seven outputs both still have 206
nodes. A source-node count does not determine a physical state count.

## One-row cylinder discovery

```sh
g++ -O3 -std=c++17 action_variants.cpp -o /tmp/zfc-action-variants
/tmp/zfc-action-variants ../../data/k218.native.tm > /tmp/zfc-action-variants.txt
python3 ../../code/verify_action_variants.py ../../data/k218.native.tm /tmp/zfc-action-variants.txt --output /tmp/zfc-variant-proof.json
```

The discovery program tests 379,757 substitutions whose targets are working
states, using a radius-three window and a matching block of fewer than 32
transitions. It discovers 62 individual replacements, each matching one
old step by exactly three new steps. The separate Python verifier checks
the complete finite cylinder cover and untouched exterior. Simultaneous
composition of independently valid replacements is not automatically valid.
