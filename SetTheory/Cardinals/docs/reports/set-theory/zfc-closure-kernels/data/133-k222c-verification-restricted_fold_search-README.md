# Restricted local-fold measurements

These exploratory tools are outside the default correctness replay. They record the limited search discussed in report Section 8.2; their negative results are not state lower bounds. The exact scope and census are in `measurements.json`.

From this directory, use an initially empty output directory:

```sh
python3 -B fold_bfs.py G226_input.tm /tmp/k222-folds-G226
python3 -B fold_bfs.py ../../portable/machine/candidate222.k.tm /tmp/k222-folds-final
```

The BFS writes a table and fold specification only upon finding a new table. An empty generated directory plus `DONE 1 best 222` therefore records a completed scan with no fold. The saved final-222 log was regenerated during packaging against the exact delivered table.
