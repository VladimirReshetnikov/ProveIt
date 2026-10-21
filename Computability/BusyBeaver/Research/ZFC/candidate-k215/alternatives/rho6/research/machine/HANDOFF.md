# Machine search and independent audit handoff

## Positive result audited

Both root-authored rho6 K215 compositions pass the independent saved-evidence and blank-prefix audit in `audit_candidate.py`. This auditor imports no supplied checker. It binds current literal tables, sources, inherited runtime implementation hashes, every ordered guarded case, positive affine clocks, row coverage, the four recorded block schemas, and a separate finite replay from a genuinely blank sparse tape. It does not rerun the symbolic derivations or claim proof-assistant kernel verification.

| Candidate | Symbolic cases | Symbolic rules | Minimum duration constant | Blank prefix |
|---|---:|---:|---:|---:|
| rho6-composition, command order210 |6176|1699838|6|95714|
| rho6-commands120 |6176|1699893|9|96284|

Both exact tables have215 working states,430 rows, all states graph reachable, native start0/dispatcher84/halt254, and canonical sorted-label start0/dispatcher83/halt215. Both reach head -8 with header57, gap1, logical registers[4,0,0,0,0,0,0,0,0], forty unit spare blocks, precisely95 one cells, and zero exterior. Both startup traces leave the two altered rows unvisited.

Both tables change exactly native199/1 from1R166 to1R12, and206/0 from0R186 to0R76, relative to their respective accepted parent. Their sources change exactly four primitive ordinals959,964,1137,1142 from register3 to5; all guarded successors and all other source instructions remain unchanged. Their mathematical row-family proof is separate, supplied by the formalism/root work.

Audit records:

- `rho6-independent-audit.json`
- `rho6-commands120-independent-audit.json`

Each includes exact hashes, current-input stability during audit, a check of the root's recorded exit0 observation, complete canonical/native row comparison, and rooted action-labelled graph comparisons against all four accepted K215 presentations and the other new variant. Every comparison is nonisomorphic. These are exact exclusions of state-renaming equivalence, not statements of behavioral inequivalence.

The runtime executions did not record prelaunch before/after manifests. The auditor explicitly does not claim such evidence; the runtime reports bind executed source/table/helper hashes, and root observation receipts record the successful process exits.

## Searches toward214

The following complete bounded searches all found no survivor. Their failures mean only that the specified bounded local proof mechanism did not certify a reduction. They imply no lower bound and no semantic inequivalence.

| Directory | Seed/family | Specifications |
|---|---|---:|
| fold-primary |accepted primary215 direct fold|632584|
| fold-commands120 |accepted command120215 direct fold|632584|
| fold-composed |accepted composed215 direct fold|632584|
| fold-rho6 |new rho6 order210 direct fold|636008|
| fold-r84-214-1 |root source rotation84/214 direct fold|632584|
| fold-r185-146-1 |root source rotation185/146 direct fold|632584|
| fold-r38-53-1 |root source rotation38/53 direct fold|632584|
| blankfold-primary |primary215 with initial15-cell window zero|632584|
| shifted-primary |primary215 shifted-head inherited-action fold|168324|
| shifted-rho6 |new rho6 shifted-head inherited-action fold|168314|
| eliminate-primary |primary215 unique-entrance state elimination|94600|
| eliminate-multi-primary |primary215 independently rewritable entrances; first-failing-entry pruning|186620|

The seven ordinary direct-fold searches total4431512 specifications; the blank-window search is separately632584. These families overlap, so totals across different mechanisms are not counts of distinct machines. Direct folds enumerate all46010 ordered distinct state pairs, inherited action choices, and all write/move/remaining-target choices for one branch when the other mapped branch agrees. Radius7/fuel97 bounds proof construction. The original invariant covers every initial tape; the blank-window variant restricts the initial radius7 window to zero and still includes the blank tape.

`folds/search.py`, `folds/filter_source.py`, and `folds/check_joint_fold.py` adapt the repository's already reviewed K217 search/checker. Only seed/state-count pins and result naming were changed for K215. The blank-window checker changes only initial abstract-domain seeding and its theorem scope. The shifted search/checker adapt `k219-shifted-fold/code/`; the checker base path and state counts were updated. All result records retain exact file hashes. Attribution remains with the inherited ProveIt search/checker authors for those algorithms.

The own `eliminate.py` and `eliminate_multi.py` use a different checkpoint relation: the deleted state occurs only inside old macroblocks; retained states match exactly. For the multi-entrance version, each new block must join before executing another changed entrance, making independently chosen entrances composable. No complete elimination was obtained. These are exploratory discovery scripts, not delivered machine certificates.

The inherited `candidate-k221/code/sim_fold.py` also reported zero both-action known-marker candidates for the primary and new rho6 tables at radius10/fuel31; only terminal tool output was observed, not a separately archived raw log.

## Other explored routes

`rewrites.py` found497 individually stuttering-equivalent one-row rewrite proposals among371090 alternatives on primary215. They are discovery output, not independently audited machine variants. Most introduce harmless detours. No pair had intersecting candidate actions on both branches after state identification, so the follow-on closure-fold family was empty. The proposals were shared with the allocator agent as possible ways to free rows.

`abstract_constants.py` performed product abstract interpretation from the calibrated logical seed with exact values0..4 plus a greater-than4 category. It found only two always-zero decrement sites4671 and4733, making primitive occurrences4672,4673,4734 unreachable. Naive replacement by unconditional CB1 increases the source DAG from202 to209; no smaller machine resulted. This experiment was not promoted to a checked formal certificate.

A proposed native164/1 shortcut omitting a PUSH was rejected as a soundness route: because164 is shared, it omits four additional AX PUSH operations at source spans beginning888,1467,2062,2412. It changes leading quantified indices to the preceding completed axiom code plusA while other occurrences ofA remain unchanged. `omit164_symbols.py`/`.txt` record the exact expression experiment. It is not a candidate.
