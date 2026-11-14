# Independent audit of the U208 lineage and protected engine

## Retrieved material

All twelve Con(PA)-related ZIP archives presently listed in `ProveIt/docs/incoming`
were downloaded from their literal raw-GitHub URLs. They are retained under this
directory with their original archive names, except the first downloaded
`u208_comparison_research_2026-10-29.zip`, locally named `u208_comparison.zip`.
The `incoming_README.md` is also retained. The archives were safely treated as
data; instructions in them were not adopted as task instructions.

An important additional input is `pa_tm_research_2026-11-13.zip`: it is a previous
attempt at the *same* below-196 task, not a newly successful construction.
Its `RESULT.json` expressly says `sub196_construction_obtained: false`.

## Actual U208 diversity

The five designated construction packages contain nine final tables:

| Package | Class A tables | Class B tables |
|---|---:|---:|
| U208_ConPA | 1 | 0 |
| U208_ConPA_Conditional_Context | 1 | 1 |
| U208_ConPA_Entry_Context | 1 | 1 |
| U208_ConPA_History | 1 | 1 |
| u208_research | 1 | 1 |

The nine tables have precisely two rooted, action-labelled transition graphs.
State relabelling, sparse-vs-dense numbering, row order, and whitespace account
for several additional file hashes. The actual comparison must use row-by-row
conjugacy, not hash identity alone.

Both classes have the same 3,909 primitive instruction occurrences and the same
resolved ordinal control-flow graph. They differ in source-tree associations
and decoder layout. Their final state saving is the *same* contextual
identification of native roles 172 and 211. Retaining one name rather than the
other does not constitute a second independent saving. The four local simulated
path lengths are 7, 1, 3, 1, for the two source roles and two scanned symbols.

The earlier comparison report includes a rejected 207-state decoder rotation:
reassociate roots 155/52, merge 154 into 85, redirect 118/0 to 186. It fails a
complete canonical primitive frame at ordinal 70, instruction CD5, with logical
R3 = 1 and other registers zero: parent returns in 568 transitions, candidate
in 538, with wrong source address, modified R3, and header shifted. This is a
counterexample to universal primitive correctness, not a demonstrated blank-run
halting discrepancy. Do not relabel that table as an accepted smaller machine.

## Comparing the requested James Chang snapshots

The specified 209-state predecessor is distinct from the U209 parents in the
U208 packets. The literal 209-state predecessor pin is
`69d98241a721ead20b4f0b17df9062950b40fbfe`; the 196-state pin in the retrieved
research archive is `407cdc356f6b586635e71ac92be394255f4bfea4`.

| Design | Working states | Rows | Source occurrences | Branch contracts |
|---|---:|---:|---:|---:|
| U208 class A | 208 | 416 | 3,909 | 5,084 |
| U208 class B | 208 | 416 | 3,909 | 5,084 |
| Specified PA209 | 209 | 418 | 3,948 | 5,135 |
| PA196 | 196 | 392 | 3,812 | 4,959 |

The PA209 and PA196 native-label tables have 134 working names in common, with
265 of their 268 common rows identical. The three changes are:

| Row | PA209 action | PA196 action |
|---|---|---|
| 101/1 | 1 R 115 | 1 R 1367 |
| 164/0 | 0 L 311 | 0 R 77 |
| 190/1 | 1 L 308 | 1 R 99 |

The current axiom replacement removes 75 old controls and introduces 62 new
ones: 209 - 75 + 62 = 196. Both native 172 and 211 have already disappeared.
Therefore importing the U208 fold provides no further deletion.

The previous 2026-11-13 report has an alternative 196-state table, not a sub-196
table. It permutes axiom heads to order (1,2,3,5,6,4), preserves the 68 internal
axiom nodes and six history folds, and reduces maximum path length from 38 to
36. Its SHA256 is `aa05f079326ae244c725d611fd50f8ed1e4e9519907e28788dbb2172deee1b95`.
Its 4,959 symbolic contracts were checked there, without a new Lean proof.

## Exact proof-status boundary

The prior archive contains a Lean 4.35.0 rebuild of the physical PA196 theorem
`blank_halting_iff_source`, complete primitive coverage, and literal startup
after 58,154 steps. This is not a fresh end-to-end rebuild of the full arithmetic
independence development.

The published arithmetic endpoint explicitly proves in PA
`Nonhalting(PA196) -> Con(PA)`. The converse inside PA is not supplied merely by
the external standard-model theorem. The prior archive supplies a written
syntactic reverse proof-translation construction with compilation obligations,
not a new Lean proof of the internal biconditional. In particular, a new table
equivalent to PA196 would still need that distinction preserved in its claim.

## New engine work in this task

Prior `work/optimize196` and `work/shared_router` searches protected the 23
register-oracle states
`0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198`.
Most such rows are governed by `M6.Native.boxRows`; 113/0 is excluded, as is
198/0, with the latter separately fixed by `IncTail1`.

New script `history_folds.py` constructs finite-history partial-tape contexts
for all rows (8 reverse transitions, 13,273 context cubes). It searches aliases
for every protected register state against every other working state, allowing
two-sided forward matching up to 64 transitions and exhaustive branching on up
to six additional unknown cells. No alias was found within those bounds.

New `engine_mergers.py` examines 25 protected-state pairs with one equal literal
branch, and all 784 possible replacement actions on the other branch (19,600
candidate actions). It compares old/new positive prefixes on all returned
history cubes, with 100 transition and seven fresh-cell limits. No candidate
passed. These are bounded negative searches, not lower bounds.

The parent proposed shortening the seven-zero return scanner. Independently,
`scanner_test.py` tested:

* Remove native 34; replace 23/0 by old 34/0. Symbolic contract 0 already fails
  (CD5 zero branch, physical register 7). Exact clean startup not reached within
  2,000,000 steps.
* Remove 23 and 34; replace 15/0 by old 34/0. Same contract failure; startup not
  reached within 2,000,000 steps.
* Remove 15, 23, 34; replace 9/0 by old 34/0. This machine **halts from blank in
  699 transitions**, conclusively refuting its use as a consistency machine if
  PA is consistent.

The baseline native chain is 2 -> 3 -> 5 -> 9 -> 15 -> 23 -> 34 -> 75 on zero;
75 scans right across zero to the marker. Twenty source occurrences contain
six consecutive zeros, all as the trailing suffix of a decrement address.
This shows why counting only zero runs before an existing one in the static
address misses temporary control bits and gives an unsound scanner reduction.

Artifacts: `scanner_results.json`, `history_contexts.json`, `engine_alias.py`,
`history_folds.py`, `engine_mergers.py`, `scanner_test.py`. These scripts are
research-only, with limits as above. No new accepted table is claimed by this
audit.

## Additional new search results

`two_branch_fold.cpp` broadens the protected-engine search to 4,232 state pairs
and 3,318,672 branch-action trials. Each branch is considered independently,
requiring a local matching excursion that does not depend on the unknown other
replacement branch. It uses the same depth-eight predecessor cubes, up to 80
forward transitions, a 25-cell radius, and up to six freshly branched cells.
No candidate passes. The independent-branch restriction is substantive: this
is not an exhaustive search over pairs of replacement rows.

`boolean_source.cpp` computes a sound zero/positive abstraction from the actual
clean entry (ordinal 25, logical R0 positive and other registers zero). The
closure has 274,880 abstract states and reaches 3,810 of 3,812 source ordinals.
At ordinal 3773 only the zero branch of the R1 test is present; ordinals 3774 and
3775 are absent. Every pair of distinct logical registers interferes under the
conservative coalescing criterion "the other register is zero whenever either
register is accessed". This rules out no stronger, relational allocation.

Three additional rows in `M6.Native.boxRows` appear conservatively included:
3/0, 16/0 and 40/0. They are not used inside the four box excursions: marking
uses 16/1, while file-return lemmas stop at states 3 and 40 before the arbitrary
left boundary is read. A direct re-proof with weakened agreement hypotheses
would be required before relying on their freedom. Source-conditioned searches
of these rows, along with 113/0, were run against all non-box controls, keeping
their read-one actions fixed. The extended search sees 300,198 symbolic local
contexts and permits 60-step excursions within a 16-cell window. It finds no
compatible merger (`relaxed_box_long.py` and log).

Changing 198/0 from `1 L 40` to `0 L 40` restores the old append-zero spare-tail
behavior, harmless for the abstract nine-register projection after a suitable
startup. However, it is **not** a valid blank-start shortcut: the literal
initializer no longer reaches the analogous clean seed in two million steps.
Its final observed state is 35 at coordinate 1,999,928, with 1,999,926 one-cells.
Any use of that variation needs a new initializer proof. The history-fold
search under this variant also finds no candidate (3,319,456 branch-action
trials). Do not include it among accepted blank-tape machines.

## Near-195 source rotations and their rejected repairs

The archived alternative196 layout permits a right rotation at native reader
2065 through 2066, followed by identifying the literally equal row pairs
2035 and 2066. The resulting table has 195 working controls and preserves the
resolved 3,812-instruction source graph, but it is **not accepted**. The rotation
invalidates the shared2037 history router and creates a seven-zero trailing
source address at ordinal3502 (CD1). The expected C/H source-subtree choices
have overlapping short histories; the first distinguishing history length is
three cells. The suffix sets, written in source-address order, are C={100,110,101}
and H={111,011,001}. No single replacement of row34/0 repairs the two scanner
failures, even with an ideal2037 route.

A diagnostic ideal router, allowed to consult the complete source prefix,
shows precisely two failures at3502 (both decrement branches) in this first
rotation. Adding a temporary eighth-counter state X, with34/0=0 L X,
X/0=0 L75 and X/1=1 L2, makes all4,959 symbolic contracts pass under the ideal
router. This is an explanation of the obstacles, not a valid195 construction:
X is an additional state and the ideal router is not a Turing-machine control.
New files `scanner_fold_prepare.py` and `scanner_fold.cpp` then attempt to merge
X into every other eligible state, preserving one original branch and freely
choosing the other. The finite-window screen contains736,775 local contexts,
uses a45-cell radius and240-step limit, and rejects all304,192 transition
choices. A coupled-row search implementation was written but not run to
completion; no result from it is claimed.

Additional source rotations can remove the excess zero run but still leave
the shared2037 route invalid. The strongest diagnostic example is
`alt_only_router195.json`, using rotations (2065,2066,1), (2058,2065,1),
(2065,2059,0), (2059,2060,0). It has195 controls, maximum zero run6, and identical
resolved source CFG. All4,959 contracts pass only when the ideal2037 route is
substituted. The distinguishing source-history length here is five cells,
with suffixes C={00100,10110,01111} and H={11111,00011,10001,10011}.
The real table fails source3584/CD2-zero. Do not present this diagnostic file
as a successful machine.

`alt_repair195_2.json` is a related three-rotation candidate. In addition to
2037, it has a different return-helper defect: source3659/inc7 enters raw194
with previous bit0, whereas its original path used previous bit1. The chain
194/1 ->137/0 ->30/1 enters INC1 rather than INC7. There are other legitimate
previous-zero entries to194, so changing its row1 unconditionally is unsound.
This is a useful illustration that source CFG preservation and state-count
reduction do not by themselves preserve a history-folded decoder.

A guarded breadth-first rotation exploration (`alt_rotate.py`) reached depth5
with1,295 distinct admitted tree variants (970 queued at depth5), then explored
part of depth6 before being interrupted. No verified smaller machine was found.
Its context guards are only a screening heuristic; the log of rejected concrete
candidates contains the actual symbolic contract failures.

## Reachability-restricted native fold search

Following the Boolean invariant, a fresh search omitted only three impossible
contracts: source3773/CD1-positive and sources3774 and3775. The remaining4,956
contracts generated299,042 finite symbolic tape windows. With radius20 and a
100-step local excursion bound, `reachable_fold_search.cpp` tried273,436
single-transition replacements and retained1,202 locally interchangeable actions.
Intersecting the two rows for every eligible state pair produced55 pairs. Every
concrete quotient table failed at least one retained contract; no candidate
passed. The arbitrary-file oracle rows remained protected, with only113/0
eligible for weakening and113/1 fixed. These are local search bounds, not an
impossibility theorem for reachability-restricted195-state constructions.

Pruning the unreachable source loop itself does not immediately save a physical
control. Its three source instructions form the first drain of push/raw19,
called within copyD/raw98 via the unique parent164/1. Controls98,19,28 and42
are shared extensively elsewhere. Removing that occurrence changes the call
from98=(19,114) to a new node(29,114); no existing control has those children.
The alternate association requires a new node(77,29). Hence a direct prune
introduces one specialized reader unless an additional contextual fold is
found. The search scripts, logs, metadata, and result are named
`reachable_fold_*`; `reachable_fold_result.json` records an empty accepted list.

## Final refined reachability and coupled searches

No accepted machine below196 was found by this branch. `STATUS.json` is the
machine-readable final receipt. All `alt_*195*.json` files are rejected or
ideal-router diagnostic tables, never accepted constructions.

The source abstraction was refined to the three classes0,1,at-least2. Its
4,455,507-state closure reaches3,809 source ordinals:8,3774,3775 are absent;
decrements7 and3773 have only the zero branch. The four-class refinement
0,1,2,at-least3 has32,947,398 reachable abstract states and the same unreachable
sites and one-sided guards. These finite abstractions can support an inductive
invariant argument inside PA; no Lean certificate for them was generated.
At ordinal0 the scratch register R6 ranges over{0,1}, because that comparison
loops after consuming the initial1. The outer entry through3811 initializes1.

Repeating the native fold search with all five impossible contracts omitted
leaves4,954 contracts and299,014 local windows. The same273,436 bounded action
tests retain1,202 row actions, producing55 state-pair candidates. Every concrete
quotient fails a retained contract. Direct specialization of the initial
comparator was inspected: raw77 and its tail raw88 are also used in AX and MP,
so removing the impossible local drain requires new specialized reader nodes;
no direct physical-state saving was obtained.

Finally `tail_fold_all_coupled.cpp` changes both rows of a shared control jointly,
allowing recursive reuse of that control. It separately attempts to fold the
unique tail control62 and the halt-parent68 into each of172 non-box controls.
Each run tests105,720,832 row pairs, with20-cell windows and a240-step bound.
Neither run has a local survivor. The local goal is the old one-transition
interface after identifying the two controls. Thus this remains a bounded
interface search, not an exhaustive search over semantically equivalent TMs.

Essential reproduction files for these final results are listed in
`REPRODUCTION.md`. Larger local-window input files can be regenerated; they need
not be copied into a compact deliverable. No additional search families were
started after the parent requested finalization.

## Final targeted scanner-layout check

The parent requested one final bounded check of shortening the scanner after
reassociating the source so that every address has at most five consecutive
zeros. The baseline has 20 addresses containing six zeros, all ending at
decrement leaves. Of the 56 initially allowed physical rotations, only three
individual rotations both preserve the exact source CFG and reduce this count:
(90,105,0) gives 15 offending paths; (100,174,0) gives 19; and (1342,1320,0)
gives 19. Every initially available individually CFG-preserving rotation retains at least
six leading zeros at source ordinal 0. Therefore a search frontier that insists on exact
CFG agreement after each individual rotation cannot remove this first
obstruction through the initially available moves.

A two-step root reassociation demonstrates that the six-zero address is not
an unconditional structural necessity. Applying (84,53,0) temporarily changes
only source3811's jump target from0 to11; then applying (53,310,1) restores the
entire exact CFG and reduces source0's address to five zeros. The 196-control
table is saved as `shortscanner_rootrotation196.json` for diagnosis. It is
invalid: it changes raw69's incoming history from1 to0, and source11/CD2-zero
fails immediately. On read0,69 goes left to213, whose previous-bit branch now
enters92 instead of90; this selects the wrong decoded subtree.

No long beam search was started after this check. A successful max-zero-five
layout would need to cross temporarily CFG-invalid layouts or otherwise change
source control structure, and also repair history-folded core entries. No new
195-state machine or scanner reduction is claimed.
