# Initialized 218-state core and the remaining startup obstruction

This directory contains an initialized 218-state implementation of the K219
source program. **It is not yet a blank-tape 218-state candidate.** The current
table enters an infinite rightward ray during its blank startup. A valid
218-state result requires a further startup repair, or an independent reduction
that leaves room for a bootstrap state.

## Concrete initialized reduction

The parent is `K219_Construction_2026-10-20`, pinned at repository commit
`26d5de6d21fa354d50e0b84fe851c289925b8d72`. Its native table SHA-256 is
`b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26`.
Delete native state 301 and make exactly these retained-row changes:

| Row | Parent | Initialized 218 core |
| --- | --- | --- |
| 87 / 0 | 0 R 301 | 0 R 88 |
| 88 / 0 | 0 R 122 | 0 L 51 |
| 51 / 0 | 0 R 16 | 0 R 122 |

The result is `candidate218/candidate.tm`, with 218 working states, 436 rows,
start state 0, and terminal state 254. Its normalized SHA-256 is
`cd2e25ad8bd58112b74d671ff78334eacc0eb237201b32c871a73424e134073f`.
The root investigator independently reconstructed the same bytes.

The sharing uses the bit immediately to the left of the decoder's current
cell. In an old-88 context that bit is 1. On read 0, the new machine takes
three steps through 51 and reaches the old successor 122 with the original
tape and head position. In an old-301 context the left bit is 0. The new
machine takes five steps through 51, 122, 137, and 30, reaching 45 with the
original tape and head position. Both old read-1 branches were already
`1 R 103`.

The retained scanner 51 has another role. During initialized execution, its
read-0 exit has a 1 immediately to the right. The old two-step exit through
16 and the new two-step exit through 122 are therefore identical, because
`16/1 = 122/1 = 0 L 1`. This fact does not hold throughout blank startup.

`verify_218_fold.py` independently replays the local identities, without
calling the search solver. On the justified post-initialization radius-7
cover it checks 1,688 cases:

| Old role / read | Cases | Old steps | New steps |
| --- | ---: | ---: | ---: |
| 51 / 1 | 1,197 | 1 | 1 |
| 51 / 0 | 441 | 2 | 2 |
| 88 / 0 | 12 | 1 | 3 |
| 88 / 1 | 14 | 1 | 1 |
| 301 / 0 | 9 | 1 | 5 |
| 301 / 1 | 15 | 1 | 1 |

All witnesses preserve every supplied tape cell, read only known cells, and
have positive duration. The root investigator additionally ran a fresh
complete symbolic primitive replay: **all 6,167 guarded arbitrary-natural
primitive interfaces passed**, using 1,515,192 symbolic steps. That stronger
interface replay is independent of the local search domain. The corresponding
artifacts are under `../root218/candidate218/`.

## Exact startup obstruction

The parent K219 initializes after 312,617 literal steps, with gap parameter 80
and 130 spare words equal to 1. The 218 core diverges much earlier. At step
79 it reaches state 51 on a 0 at head coordinate 5, with another 0 to its
right. The old table uses `16/0 = 1 L 1` to create a new rightmost sentinel.
The new table uses `122/0 = 0 L 137`, eventually reaching state 35 and writing
1s forever to the right into blank tape. This is a provable ray, not merely
a finite timeout.

The startup-inclusive local check has five failures, all in the scanner's
read-0 role. Their radius-7 window integers are `1, 5, 43, 53, 56`. No other
local case fails. `candidate218/full_witnesses.json` and
`candidate218/local_proof.json` retain the precise boundary of the result.

`extend_fold_windows.py` covers initialized execution of the new core by
mapping the parent windows and adding every new intermediate position in the
checked macro witnesses. Newly exposed fringe bits are widened independently.
The resulting `candidate218/windows_postinit_r7.txt` has 114,083 patterns over
all 218 working states, SHA-256
`3fb97e6c9e685842fa861252130d2312844ff7c308d606126e82260ea7ca1067`.
This file makes no claim about reachability from the new machine's blank
start.

## Fresh K219 coverage

The K219 source invariant and window projection were regenerated; the earlier
K220 gap-117/spare-167 premises were not reused. The source product invariant
starts at logical registers `[3,0,0,0,3,0,0,0,0]` and uses unions of the five
classes `{0}`, `{1}`, `{2}`, `{3}`, and `{n >= 4}`. Its independent closure
check covers all natural values, not a finite register sample.

The full radius-7 cover in `windows219/windows_r7.txt` has 115,188 patterns;
the post-initialization cover has 113,447. Both cover all 219 native states and
all 6,162 seeded guarded symbolic families, including the halting interface.
The difference between that family census and the 6,161 source-CFG closure
edges is intentional: projection includes every mask-enabled guard and the
halting family, rather than counting only nonterminal CFG edges.

An independent differential audit checked 480 concrete primitive instances,
823,114 literal step windows, and 48 block schemas. The projection itself is
based on symbolic unary/list induction and conservative affine-run widening;
the concrete audit is supporting evidence, not the source of unbounded
coverage.

A selected-role radius-10 projection also completed for native states
`1,4,16,40,54,103,108,113,198,301,302`. It contains 76,853 full and 75,924
post-initialization patterns. It may only be used for transformations whose
mutated states are all among those eleven roles. Missing-state contexts must
never be interpreted as empty reachable domains.

A second radius-10 projection, specifically for the initialized-fold roles
`51,88,122,137,301`, is in `windows219_r10_foldroles/`. It covers all 6,162
seeded symbolic families and has **28,168 startup-inclusive** and **28,125
post-initialization** patterns. The full counts by state are 27,846 at 51,
38 at 88, 27 at 122, 222 at 137, and 35 at 301. The projector is
`project_target_windows219.py`, SHA-256
`3b5276c8c3127a74a0f9a36a4b4ce62b5dd590b853fa6ca65dd716be723fe763`.
It uses the same proved gap-80/spare-130 premises and the independently
checked source invariant. `audit_foldrole_windows219.py` independently
replayed 823,114 literal steps and checked all 19,159 selected-state windows
against this cover, with no missing window. As with the earlier audit, this
is finite regression support for the symbolic projection argument, not a
replacement for that argument. This selected-state file does not supply
contexts for any of the other 214 working states.

## Main bounded synthesis results

Every negative statement below is restricted to the specified finite search
family and supplied conservative window cover. None is a state-count lower
bound or an impossibility theorem for a different protocol.

The coordinated existing-helper search on all 261 common-branch K219 pairs
has exactly one output: the 88/301/51 initialized reduction above. The more
general four-row search independently rediscovers that same output. It is
not a second distinct reduction. In particular, do not summarize the
261-pair batch as having zero outputs.

The original four-row decoder search considered seven keep states against
301, with all 217 remaining helper choices: 1,519 jobs. Of these, 1,516
completed, three timed out, and one completed job produced the initialized
reduction. The three incomplete jobs are explicitly retained in the receipt.

Additional completed or explicitly bounded searches include:

* The eight halt-inclusive core families on the original 219 table, the
  independently proved alternative 219 table, and their composed
  157/160/161 helper variants: no additional reduction.
* All incoming one-step head/write gauges for the 88/301 merge on the full
  startup-inclusive cover: 651 jobs, 645 completed, six timed out, no output.
* Full four-row 88/301 searches on the alternative 219 and the neutral-helper
  219 layouts: each 217 jobs, 216 completed, one timed out, no output.
* Full six-row synthesis on states 88, 51, and either 36 or 16, preserving all
  their old roles and the old-301 role: both completed without output at
  old-trajectory bound 50 and new-run bound 128. They examined 691,819 and
  1,840,072 row choices respectively.
* The same six-row architecture with all 216 possible extra helper states,
  while keeping the 88/1 and 51/1 rows unchanged: all 216 jobs completed
  without output. Freeing 88/1 while keeping 51/1 fixed completed 178 of 216
  jobs, with 38 timeouts and no output.
* Four jointly free read-0 rows at 88, 51, 122, and 137, with their read-1 rows
  unchanged: exhausted in 7,276 choices, with no output. Allowing exactly one
  of those four read-1 rows to change also completed in all four cases, with
  no output.

The continuation-based `multi_row_propagate.cpp` carries unresolved window
executions through partial row assignments instead of redoing already proved
cases. It reproduces the known initialized reduction with the same 16,142
choices and 311 search nodes as the independent original backtracker. It also
reproduces the four-zero negative with the same 7,276 choices and 15 nodes.
Search completion and timeout logs remain the authority for any larger run.

`multi_row_mrv.cpp` additionally performs forward checking on remaining row
domains and selects the smallest supported domain. The more informative
radius-10 fold-role cover was used to repeat the four-free-zero-row family
and all four families that also free exactly one read-1 row. Every one
completed at old-trajectory bound 50 and new-run bound 128, without output:

| Additional free read-1 row | Row choices | Search nodes |
| --- | ---: | ---: |
| None | 7,299 | 12 |
| 88 / 1 | 8,875 | 52 |
| 51 / 1 | 7,492 | 14 |
| 122 / 1 | 14,603 | 120 |
| 137 / 1 | 13,989 | 178 |

Unrestricted eight-row synthesis on 88, 51, 122, and 137 did **not** finish.
The continuation search timed out after 60 seconds at old/new bounds 3/64,
and after 120 seconds at bounds 50/128; the corresponding MRV searches also
timed out. None produced an output before its time limit. These four runs
are incomplete explorations, not exhausted negative families. Their exact
counts, input hashes, and logs are recorded in
`final_local_synthesis_receipt.json`.

## Attempts to free a bootstrap state

The initialized 218 table was searched afresh for a 217-state initialized
core. The eight global bounded fold families all completed without output.
The same eight families also completed without output on an initialized
218 table obtained by composing the independently checked 157/160/161 helper
changes. The latter composition is independently replayed by
`compose_fold218.py`; it checks all 1,688 positive local identities and
produces a 116,492-pattern initialized cover. Its table SHA-256 is
`051e4b2195d64097cfd90020caaea7ffa1a612fd6718c641911d26b13591e24e`.

More general four-row merge/helper searches on the initialized core examined
the pairs 0/51, 16/122, and 36/51, with every one of the 216 possible retained
helper states. Of 648 jobs, 645 completed and three timed out; none produced
a reduction. These are stronger transformations than simple identical-row
identification, but still a finite local architecture.

## Finite bootstrap repair screens

The source team justified a broader clean logical seed form
`[n,0,0,0,d,0,0,0,p]`, with arbitrary naturals `n,d,p`. The finite bootstrap
screen therefore accepts those values, any nonempty finite natural spare
list, and any legal nonnegative extra gap. A seed hit is only a finite tape
witness: modified primitive semantics must still be proved independently.

All 218 possible designated initial states of the unchanged 218 core were
checked. Every one enters a provable outward blank-ray self-loop. No choice
of start state alone repairs startup.

Arbitrary one-row changes were screened at the 41 distinct initial-trace
rows other than 66/0 and 198/0, using all 872 existing write/move/target
actions. The weak-seed screen found exactly two actions, both at 36/0:

| Changed row | Clean seed time | Gap | Spare file |
| --- | ---: | ---: | --- |
| 36/0 = 1 L 6 | 169,917 | 12 | ten 0s, then eighty-two 1s |
| 36/0 = 1 L 10 | 166,045 | 12 | nine 0s, then seventy-eight 1s |

Both seeds have all nine primary registers equal to zero. **Both patches
are invalid repairs:** independent primitive probes show they split a
primary unary block and shift later primary registers. Their behavior is
not confined to the spare tail. The finite seed witnesses are retained as
counterexamples to treating initialization success as compiler correctness.

The separate single-198/0 screen has no weak-seed hit. Nine arbitrary
two-row screens among the CI-tail states 0, 94, 66, 97, and 198 also have no
weak-seed hit: these nine runs enumerate 42,728 reachable second-row
assignments in addition to 872 outer actions per pair. The remaining
66/198 pair is owned by the root investigator. Dynamic branching enumerates
the second row only if it is actually reached; changing an unvisited row
cannot change that bounded prefix.

The proposed two-zero-spare append patch
`198/0 = 0 R 97, 97/0 = 1 L 54` fails from blank at step 90, reaching the
same kind of outward state-35 ray. All alternative designated start states
also fail for that patched table.

These finite searches use a 3,000,000-step limit and a 65,536-cell storage
window, with exact rejection of provable outward self-loop rays. Runs
ending at the numeric limits are bounded exclusions only. The reports do
not extrapolate them to unbounded nonexistence.

Finally, `neutral_multi_boot.cpp` relaxed the requirement of reproducing
the old startup trajectory. It synthesized changes to all eight rows of
88, 51, 122, and 137 that preserve the **initialized 218 core**, and then
tested each resulting table from every designated initial state on blank
tape. This run uses the independently extended post-initialization cover,
not the old machine's startup-inclusive cover. It timed out after 180
seconds with 6,094,848 row choices and 198,009 search nodes. Fourteen neutral
tables were found; all 3,052 corresponding blank-start tests failed to
produce a weak clean seed within the stated limits. The run is incomplete,
and the fourteen tables do not exhaust this architecture. The implementation
also rejects exact translated cycles when the full nonzero support has span
less than 128; this is separate from rejecting simple outward blank rays.
The identity-quotient smoke test on states 0 and 94 agrees with the independent
two-state solver: one neutral table and no bootstrap hit among its 218 start
states.

## Artifact boundaries

The initialized reduction, local proof witnesses, exact failed startup,
fresh runtime replay, and conservative window covers are reusable results.
They isolate a specific missing condition: the scanner's empty-tail
bootstrap behavior must coexist with its new decoder phase. A future
candidate must resolve that condition or provide a different independently
verified blank initialization. No file in this directory currently removes
that final obligation.

This report and `final_local_synthesis_receipt.json` were frozen after the
five completed radius-10 row-synthesis runs and the initialized-only
eight-row timeout. Further results produced by the source or root teams are
not silently incorporated into these counts.
