# Search for a 193-state AX11QH5 decoder

This is a bounded unsuccessful search, not an optimality proof.

The source is adapted from the PA194AX11 packet's `ax11_grammar` search.
The starting grammar is the new AX11QH5 emitter; the fixed table is its
coefficient-five runtime. Unlike the inherited scorer, this scorer considers
history folds involving eligible fixed controls as well as reader controls.
It rejects an incoming context that moves left, and records the actual
written history bit. Simultaneous proposed folds are checked on all four
two-cell contexts before the score is accepted. Source and complete tape
validation would still be necessary for a successful proposal.

The new construction has 135 fixed controls, 67 raw readers, and eight
compatible folds, hence 194 states. A score `nodes - folds <= 58` is necessary
for a 193-state result. The actual run made 2,713,285 proposals and accepted
104,685 moves in 240 seconds. Its best score was 59, and it saved no score-58
hit. These are proposal counts, not counts of distinct machines.

Reproduce the same search family with a C++17 compiler:

```
c++ -O3 -std=c++17 search.cpp -o search
./search seed.txt leaf_attrs.txt rerun 240 2026111401
```

The seed and all inputs are frozen. The elapsed-time stopping rule means
that iteration counts may differ on another machine. The output contains
unverified grammars, not additional accepted consistency machines. Exact
construction and verification of AX11QH5 do not depend on rerunning this
heuristic search.

`local_fold_opportunities.json` records a separate exhaustive check within
the simple two-cell provider-fold form: the raw table has exactly its eight
used opportunities, and the final table has none of this form. That statement
does not exclude longer-history folds or changes to the source or runtime.
