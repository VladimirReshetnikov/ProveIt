# Independent source review: K215 first node chunk

`check.py` compares the exact bodies of the three 487-entry tables with the current original source and the matching failed-rebuild snapshot. It pins those files, the draft files, the original RMEquiv source and the two authenticated fresh-base object bytes. It checks the proposed predicate and arguments and confirms that the original `wfCheck` contains the same `nodeOkb` check, whose body has eight Boolean clauses.

The proposed theorem checks indices 0–31. The other 455 indices, four root conditions, relation between the copied tables and the original module in Lean, and assembly are outside this probe. This is source review only: it does not establish that the theorem compiles, is true, or fits the resource limits. No Lean run was made.

Run with `python3 -I -S -B reviews/current14-k215-wf-chunk-probe-source-independent/check.py` from the DiophantineConsistency directory.
