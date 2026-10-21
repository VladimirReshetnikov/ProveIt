# Late upstream alternatives: limited structural preflight

Input: K219_Alternatives from public upstream commit ffcdff81.
This check uses its upstream-label tables, where the two new labels are
301 and 302, matching the earlier K219 reference numbering.

Nine tables were inspected: the three upstream alternatives, each unchanged
and with either of our single-row MP-success patches at 164/1. The copy
patch is 1 R 114; the cache patch is 1 R 130. Those rows do not overlap the
upstream changes. This disjointness alone is not a proof of combined source
or runtime calibration. No baseline finite fixtures were applied to the
retagged sources.

Every table has 219 graph-reachable working states. Partition refinement
starting with one working-state class and a separate halt class, and refining
by each symbol's write/move/successor-class triple, yields only singleton
working-state classes. Thus this strict transition bisimulation and ordinary
graph reachability give no immediate state reduction. They do not rule out
context-sensitive, delayed, or source-semantic reductions.

receipt.json records all results and the newly common transition branches.
Those pairs are structural leads, not validated folds. The three distributed
upstream-label tables are copied here for exact identification. No machine
with 218 or fewer working states has been produced by this preflight.

## Bounded follow-up on zero_terminal only

The unchanged zero_terminal table passes all 6,646 combined whole-gate, NIP,
MP, refill, and remaining ordinary fixtures. The two fixed-common-branch
merge families then exhaust all 876 replacement actions each with no
survivor. A broader arbitrary-both-rows search hits its 110-second timeout
before reporting a complete pair; it is partial and must not be reported as
exhausted. See zero_terminal_search_receipt.json and the exact logs.
