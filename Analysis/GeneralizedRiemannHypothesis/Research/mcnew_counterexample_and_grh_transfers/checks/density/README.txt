Run python check_density.py with assertions enabled. The script uses the standard library.

lower.csv contains one threshold and one sorted set of 7-smooth integers per row. A new row increases the permitted cardinality by one. The sets are checked separately and may differ from earlier rows.

intervals.json gives the seven cutoff intervals and explicit lower-bound sets for the independent 11-adic layers. The .json.gz files in trees/ rule out a putative 11-smooth independent set larger than the corresponding cap. Internal nodes branch on one vertex. Leaves carry a contradiction, an exhausted deletion budget, or exact integer weights on uncovered triples. See the report for the inequality verified at each leaf.

The density integral and all target comparisons use integer or rational arithmetic. The decimal representations in verification.txt are for reading convenience.
