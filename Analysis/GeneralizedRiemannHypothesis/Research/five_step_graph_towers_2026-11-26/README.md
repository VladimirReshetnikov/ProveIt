# Five-step spanning-tree divisibility

The report gives a proof for p = 11 at every layer, plus an exact finite check
for every prime from 11 through 101. The result is unconditional and addresses
the odd-step question in the linked ProveIt reports.

- Rebuild the manuscript: pdflatex five_step_graph_towers.tex (twice).
- Reproduce the CSV with Python 3: python3 verify.py 101 > replay.csv
- Compare with the enclosed result: diff -u maxima.csv replay.csv

The same run checks the twelve projective depths and independently computes
the first-layer reduced Laplacian determinant for the p = 11 witness.
Counts refer to normalized triples, not equivalence classes.
