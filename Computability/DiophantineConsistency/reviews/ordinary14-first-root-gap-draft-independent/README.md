# Independent source review: first-root gap

From k≥8m+4, monotone multiplication yields `2mk+m≤k²`. Multiplication by nonnegative m and the first Pell norm give `(mk+m)²<tau²`; nonnegative square reflection and s≤m imply `mk+s<tau`. The standalone source needs no graph, root sign or parent witness; its positive-m hypothesis is retained.

The checker tests finite Pell recurrence cases, pins the previously passed large-k review, and replays the author's source receipt. It does not rerun that review or elaborate Lean. Run `python3 -I -S -B check.py` and compare with `result.json`.
