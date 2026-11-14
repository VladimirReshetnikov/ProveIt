# Association search below 194

Pinned source corpus: ProveIt 768c2be1a8e4d2fcf8aa3443c7b0f084d145734c.
A is the unnumbered incoming PA194 ZIP, with 67 raw AX readers and 7 folds.
B is the `(2)` ZIP, with 68 raw readers and 8 folds. Both have the same 190-token
emitter and the same 134 fixed controls. The two macro words were checked equal.

## Search rule

`association_search193.cpp` is the inherited exact-compatible-fold search with
target changed to 59 net AX readers (134+59=193), started from A and B.
Moves rotate one occurrence or every occurrence of a shared binary subtree.
All proposals preserve the macro word. The fitness is allocated AX readers
minus simultaneously certified two-cell history folds, together with inherited
scanner/address penalties. The exact finite local simulation is repeated on
the entire proposed simultaneous quotient, so counting incompatible pairwise
opportunities is avoided.

`plateau_search193.cpp` closes the same rotation rule within score 60 and
zero penalty. Both baseline shapes are seeds. It retains all unseen score 60
successors; its 20000-entry pool bound was never reached. It completed 11472
parent expansions and 2373136 newly evaluated neighbors, with an empty queue.
There were 11470 retained nonseed shapes. No candidate scored 59. Deduplication
uses a 64-bit hash of the expanded association, so this is a bounded computer
search statement, not a mathematical lower bound or collision-free proof of
exhaustive enumeration.

`mixed_association193.cpp` broadens the fold candidate domain to every
non-box control except the initial control. It collects every incoming row:
a right move records its written predecessor bit; a left move makes the
simple predecessor-bit premise unavailable. This matters because examining
only bit-preserving incoming reader edges would be unsound for arbitrary
fixed controls. The same exhaustive local simultaneous-quotient check applies.

`mixed_exact193.cpp` additionally closes each selected quotient under literal
identical-row merging. Such an extra quotient is unconditional. It may create
new duplicate rows after redirecting destinations; these are merged in turn.
It is only a sufficient rule and does not compute arbitrary TM equivalence.

The Combined core changes six fixed rows, and the Combined+zerojump core
changes one more. Their mathematical source calibrations and complete
runtime checks are supplied by the construction/theory subtask. Association
search itself does not certify the PA consistency equivalence.

The exploratory parameter run changes independent head parameter permutations
and head order; its log has no improvement. Its early saved same-size files
can differ only in unused metadata, so they must not be advertised as new
constructions. They are not retained as deliverables.

## Reproducibility and limits

The static input files include every fixed row, terminal state, scanner
attribute, initial word, and initial association. A complete search run is
reproducible using the recorded seed and cycle count. Interrupted searches
are reported only through the last completed progress record; unlogged tails
are excluded. Counts are proposal slots, not distinct tables, except for the
explicit plateau `tried` count. No negative result is a state-count lower bound.
The search output requires source-CFG binding, symbolic-runtime verification,
exact startup, and a local quotient certificate before it can support a new
machine construction. A low search score alone is insufficient.

## Final bounded outcome

The eight recorded annealing runs completed 49,284,000 logged proposal slots in
total. This includes repeated proposals and repeated machines across runs.
Both the original-fold and the mixed-fold Combined plateau traversals closed
after 11472 parent grammars and 2373136 newly evaluated neighbors, with empty
queues. The Combined+zerojump traversal with exact duplicate-row closure was
stopped after the logged 5600-parent prefix, containing 1163952 newly evaluated
neighbors and 1688 pending grammars. It was not exhausted. None of these searches
reported a zero-penalty allocation below 194. The minimum raw AX-reader count
on the completed plateaus remained 67. All ongoing processes were interrupted
cleanly before the logs and exact finite-prefix counters were frozen.
