# Reproducible grammar searches

`search_summary.json` gives exact frozen inputs, executable names, time budgets, seeds, observed counters, and completion status. A running checkpoint is not reported as a completed search. The inherited fixed-runtime score convention is 134 plus the effective score; the radix screen includes its extra fixed control in the score. Safety penalties are heuristic search filters, not certificates.

For each row, compile PROGRAM.cpp with a C++17 compiler, then run:

```sh
c++ -std=c++17 -O3 PROGRAM.cpp -o PROGRAM
./PROGRAM TEMPLATE ATTRIBUTES fresh_output_prefix SECONDS SEED > fresh_output_prefix.log
```

The commands must run from this directory because the C++ sources include their neighboring screen implementation. Keep recorded logs unchanged when rerunning. Wall-time termination means different machines and loads can produce different mutation counts even with the same seed.

The ordinary-h6 h5X search nominated PA194H5X; the ordinary-h6 positive-join search nominated PA194JH5X. Their fixed tables and complete independent certificates are in the corresponding machine directories. For PA194H5X, its exact reconstruction uses the frozen grammar and folds in `../../construction/`, not this stochastic program. Other recorded score-60 grammars can be alternative associations of the same word. No count of hit occurrences is a count of independent arithmetic consistency proofs.

## Final cutoff and additional finite screens

All 18 recorded randomized runs completed at their listed budgets. They performed 187,622,892 mutation trials and accepted 31,317,681 mutations. These counters do not count distinct grammars, transition tables, or semantic designs. No run established a machine with fewer than 194 states. `FINAL_SEARCH_RECEIPT.json` records the aggregate and final per-run counters.

`J_full_order` allows all six schema heads to change order and tracks the changing head lengths when permuting parameters. `H5X_relaxed_height` raises only the inherited source-height heuristic threshold from 38 to 46; the exact table and full source checks would still be required for any nomination. Neither found a smaller nomination.

The two additional finite screens use the frozen J machine as input:

```sh
c++ -std=c++17 -O3 price_J_orders.cpp -o price_J_orders
./price_J_orders J_full_order.templates.txt leaf_attrs.txt fresh_order_prices
c++ -std=c++17 -O3 price_J_chunk_orders.cpp -o price_J_chunk_orders
./price_J_chunk_orders J_full_order.templates.txt leaf_attrs.txt fresh_chunk_prices
```

The first enumerates all 720 head orders at the frozen complete binary-tree shape, with minimum raw effective reader score 60. The second preserves the six extracted head subtrees and the prefix/suffix subtrees, enumerating all 720 orders and 429 binary associations of eight chunks, for 308,880 candidates; its minimum raw effective reader score is 67. The minimum for the second screen was recorded independently of its heuristic penalties. These are finite comparisons in explicitly stated grammar families, not global state lower bounds.
