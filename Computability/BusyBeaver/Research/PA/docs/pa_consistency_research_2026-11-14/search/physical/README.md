# Bounded physical contraction experiments

`contract_search.py` computes the least radius-six blank-start window closure and searches old execution blocks of at most 31 transitions that have exactly one transition's tape effect. The full tracked window is preserved except for the initial head cell, and the net head movement must be one cell. Each row action is retained only if it works for every abstract window admitted at that row. Z3 chooses among those actions to minimize the graph-reachable state labels.

The script requires the Python `z3-solver` package. From the archive root:

```bash
python3 search/physical/contract_search.py audit/selected196_tables/00.tm /tmp/contractions_original
python3 search/physical/contract_search.py audit/selected196_tables/20.tm /tmp/contractions_separate
```

Both completed experiments retain 196 states. They find two nontrivial row options, corresponding to already identified bypasses. The output state count is a minimum for the enumerated row choices and reachability encoding, not for arbitrary Turing machines.

The additional `new_layout_folds/` and `contract_folds/` receipts record helper scans performed with the pinned ProveIt `Computability/BusyBeaver/Research/PA/pa196-vs-u208/search` tools. These are compact evidence receipts, not a self-contained copy of that entire external search toolkit. The original source and commit are given in the top-level README. Their empty survivor results have only the reported scan scope.
