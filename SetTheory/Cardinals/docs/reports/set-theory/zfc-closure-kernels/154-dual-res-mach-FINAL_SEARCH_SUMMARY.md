# Machine-side research: K220 phase

## Status and change of target

No new 219-state machine was established by these searches. The repository has
subsequently acquired a 219-state candidate, and the user has changed the
target to at most 218 states. The broad K220 jobs were stopped at that point;
their completed receipts are retained. This note is a checkpoint of the K220
phase, not a claim that the new target is impossible.

The K220 input was the native table in
`K220_Construction_2026-10-20/machine/k220.native.tm`, SHA-256
`4466ec4f947a9c5112397c30ca25b0e70e3ac39ee54878b3e4493a0297d732e4`.
Its source SHA-256 is
`837e92d7b1c107330f160f654f6c36ff0b03dfbf6bc2b89c6f782eb7db4c4ce7`.
It has 220 working states, native start 0, dispatcher 84 and halt 254.

## Positive results: two new MP implementations compile correctly

The root agent constructed two logically motivated variants of forward modus
ponens. The formalism agent supplies their separate logical calibration:

| Source variant | Working states | All symbolic primitive cases | Symbolic proof steps |
|---|---:|---:|---:|
| `no_push_copy` | 220 | 6,142 | 1,512,559 |
| `no_push_cache` | 220 | 6,137 | 1,511,753 |

Both passed the inherited symbolic runtime checker on **all independent natural
primary register values at each decrement guard**, arbitrary natural extra
header gap, arbitrary first spare value, an arbitrary finite remaining spare
list, and the complete tape including its zero exterior. Each proof rederives
the four list-block traversal lemmas from the supplied literal table. The
proof-construction loop limit does not bound represented register values or
actual machine runtime. These are executable mathematical induction checks,
not proof-assistant kernel certificates. They certify primitive compilation;
source calibration and blank initialization are separate obligations.

Receipts: `runtime_mp_copy/runtime.json`, `runtime_mp_cache/runtime.json`, and
their `cases.json` files. A fresh replay using the standalone driver also
completed for `no_push_copy`: `runtime_mp_copy/portable_runtime.json` and
`portable_runtime_cases.json`. The root agent independently checked both
blank initializations: the inherited 409,835-step complete initial frame.

## Finite whole-primitive search and its limits

`whole_primitive_frames.py` generated 6,162 baseline frames, one for every guard
admitted by the root agent's finite source abstract interpretation. Each input
uses the independent minimum allowed value of each register, spare list `[1]`
and extra gap 0. All 440 transition rows occur in these reference runs. Their
2,952,740 literal steps were checked against the independent primitive
specification; the longest reference run has 680 steps.

These Cartesian minimum frames are **not claimed to be reachable on the
actual blank-tape run**. Source masks overapproximate reachability and omit
relations between registers. Conversely, passing these finite tests does not
establish correctness for larger register values or arbitrary spare lists.

The generalized endpoint oracle requires the correct next source PC and the
correct nine primary values, but permits integer translation of the complete
frame, any valid header gap of at least 64 cells, and arbitrary spare values
with at least the input number of blocks. Halting source instructions may
halt with arbitrary final tape. Runs stay inside a 512-cell test window and
have a finite execution budget of `4 * reference_steps + 1600`, measured from
the cached first modified-state visit when prefix caching is enabled, and
from the initial frame otherwise. Failure under this oracle is a bounded
search rejection, never a state lower bound.

The alternate frame cut at native state 75, one cell left of the usual code
origin, allows deletion of dispatcher 84 to be considered. For pair families
involving 75 the adaptive cut uses dispatcher 84 instead. Every complete
search first reruns all baseline frame controls.

### Completed baseline families

| Family | Exact completed scope | Survivors on all finite frames |
|---|---:|---:|
| One common transition branch, arbitrary other retained row | 266 pairs; 234,080 row actions | 0 |
| Delete a state with one incoming row, synthesize that row | 110 states; 96,800 actions | 0 |
| Both retained rows arbitrary, original one-common-branch pairs | 266 pairs; all 880² assignments per pair covered by rejection or execution | 0 |
| Both retained rows arbitrary, two-different-branch disjoint-window pairs | 10,984 pairs; all 880² assignments per pair covered | 0 |
| Further overlapping-window pairs | 640 complete pairs out of an additional 12,840-pair family | 0 |
| Tape-tagged dropped role, both retained rows arbitrary | 266 pairs in each of three incoming-write tag conventions | 0 |
| Delete 47 via `(31,1)=(1,R,121)`, repair any one other retained row | 384,560 mutations | 0 |
| Delete 47 via `(31,1)=(1,L,87)`, repair any one other retained row | 384,560 mutations | 0 |
| Extra single-row repair of sole-deletion witness survivors | 103 complete recipes of 113; 384,560 actions per completed recipe | 0 |

The three tag conventions flip the bit written by incoming transitions to
the dropped state: all incoming transitions, only left-moving incoming
transitions, or only right-moving incoming transitions. This permits the
role distinction to be stored on the tape and recovered by a shared helper.

The 10,984-pair family was completed in four phases. The first three disjoint
prefixes contain 300, 4,420 and 6,216 pairs. Forty-eight remaining pairs
involving state 75 are covered by a separate completed 180-pair run (the
other 132 overlap those prefixes). The family union is therefore 10,984,
not the sum of all four raw run sizes. The later overlap-family checkpoint is
480 sequential pairs plus 40 completed pairs in each of four disjoint
round-robin chunks. Thus **11,890 distinct baseline state pairs** have a
complete two-row finite screen, out of 24,090 possible pairs. The remaining
pairs were not completed when the target changed.

The common-branch two-row run instantiated 64,888,560 complete row pairs after
partial-execution pruning. Its 96 initial witness survivors all failed
another admitted frame. Partial pruning stops at the unspecified retained
row and only rejects an assignment if it fails before reaching that row;
the unspecified row cannot affect such a failure.

Principal receipts are the `whole_primitive/general_both_common.log`,
`general_both.log`, `general_both_pre.log`, `general_both_pre2.log`,
`anchor75.log`, `phase_progress.json`, `overlap_remaining.log`,
`overlap_partition.json`, `overlap_chunk_*.log`, `tag_both_*.log`, and
`sole_second_repair/results.json` files. The two-row action count is 880
because deletion leaves 219 working targets plus the halt target, with two
write choices and two move choices.

### Alternative 220-state layouts

The same one-row pair and sole-deletion searches were completed on the
repository's `row103`, `row157`, and combined all-tape alternatives; on the
six-leaf zero-NOP variant, its row160 variant, the occurrence-row160 variant;
and on the safe rho6 argument-permutation variant. All were negative under
the finite oracle. The six-leaf NOP and rho6 variants also received completed
two-row common-branch screens (268 and 267 state pairs respectively), with
no survivor. These numbers are family sizes, not formal impossibility bounds.

Weak source reassociation plus complete guarded-CFG equality and decoder-node
binding produced 162 distinct layouts within two rotations of each of three
roots: baseline K220, `no_push_copy`, and `no_push_cache`. For each root, 109
layouts passed every finite baseline primitive control and 53 failed before
mutation search. None of the accepted layouts yielded a one-row pair or
sole-deletion survivor. Source and decoder checks alone were insufficient:
some rewritten decoder states also have arithmetic roles.

Receipts: `whole_rotations/results.json`,
`whole_rotations_mp_copy/results.json`,
`whole_rotations_mp_cache/results.json`.

## Earlier local proofs and rejected candidates

A radius-five global window invariant had 90,539 contexts. Symbolic traces of
all baseline primitive cases, unary self-loop closure, conservative fallback
for eight list-traversal states, and the exact blank prefix reduced this to
35,562 contexts. The result is a coverage domain assembled from those proof
pieces, not a claim of ordinary unrestricted global dataflow closure.

On the latter domain, exact local simulations found no one-common-branch fold
(234,080 actions), no tested two-branch rewrite (9,715,200 actions), and no
tested displacement-by-two rewrite (48,191,440 actions). Earlier wider-domain
searches are also retained. These are stricter local endpoints than the later
whole-primitive oracle and should not be mistaken for exhaustive compiler
optimization.

Two apparent folds of states 42 and 47 passed source-prefix-local reasoning
but failed complete CI6 execution: they incremented logical register 5
instead of register 6. Arithmetic callers of state 42 invalidate the narrow
prefix invariant. The root agent supplied concrete complete-frame failures
and exhaustive specified two-row repair screens. Similarly, 42 source-only
selector eliminations involving state 144 or 161 were rejected by concrete
source-mask-admissible minimum frames at CI4 or CI3. A symbolic checker
exception such as “unknown run may be empty” was treated as **not proved**,
not by itself as a counterexample; concrete execution supplied the failures.

The clear-loop quotient experiment permits a register to vary while it is
being cleared, requires a complete clear loop to terminate before the next
observation, and compares only live primary fields at the exit. It found six
literal clear loops and their six continue sites with one dead field; nearly
all other sites retained all nine live registers. Completed baseline and
combined-alternative pair/sole screens were negative. See
`clear_liveness/analysis.json` and its logs.

## Portable replay tools

`verify_runtime_portable.py` takes an **extracted** inherited K221 package:

```sh
python3 verify_runtime_portable.py \
  --baseline /path/to/K221_Construction_2026-10-20 \
  --table /path/to/candidate.tm \
  --sites /path/to/sites.json \
  --output /path/to/runtime.json
```

The K221 archive is nested inside the inherited K220 package at
`portable/vendor/K221_Construction_2026-10-20.zip`. The driver uses the
symbolic checker, independent runtime helper and native-to-legacy map from
that extracted package, and records their hashes. It validates complete
binary source codes and total two-symbol working-state rows. No repository
checkout or nonstandard Python dependency is required. Assertions must be
enabled. Failure returns `NOT_PROVED`, not a mathematical disproof.

`generate_frames_portable.py` regenerates the finite fixtures from a table,
source and supplied source-facts JSON. A fresh replay reproduced baseline
`frames.bin` and `witnesses.txt` byte for byte (the frame SHA-256 is
`8b8621d7989118418008853bb0d8553b4cd00730fa168d418b18a5ab94f935f3`).
The C screen is standalone:

```sh
cc -O3 -std=c11 -Wno-unused-result whole_primitive_folds.c -o whole_primitive_folds
GENERAL_FRAMES=1 FRAME_ANCHOR=75 ADAPTIVE_ANCHOR=1 \
  ./whole_primitive_folds candidate.tm frames.bin witnesses.txt hits.txt \
  both_pre common_pairs.txt
```

Omit `both_pre common_pairs.txt` for the one-common-branch single-row family;
replace it with `sole` for sole-incoming deletion. `FIXED_REPAIR` is a
six-integer environment value `parent read dropped write move target`, where
move is -1 or +1; it searches an additional changed row. `DROP_TAG_MODE` 1,
2 or 3 selects the three incoming-bit tag conventions. The optional exact
quiet-cycle rejection detects a repeated state/head pair since the last
tape write that changed a cell; it is disabled unless `CYCLE_PRUNE` is set.
The completed principal receipts used the default without that shortcut.

The rotation driver and its helper accept `BASELINE221`, `BASELINE220`,
`SEARCH_TABLE`, `SEARCH_SITES`, `WHOLE_ROT_OUT`, `ROT_FRAME_META`, and
`ROT_WITNESSES` as path overrides. `whole_rotations.py` itself does not need
the legacy repository fold scripts. Its output records baseline-control
failure separately from a negative mutation screen.

## Rebase to the repository's K219 candidate (updated target: 218)

The user subsequently reported a new 219-state candidate. Searches were
rebased to `baseline219/K219_Construction_2026-10-20`; the new target is at
most218 working states. Its native table has SHA-256
`b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26`.
The ordered source has206 distinct DAG nodes and4,744 primitive leaves.
The parent independently replayed the complete inherited proof, including
blank initialization. These are properties of the supplied219-state
baseline, not a new218-state result.

### Finished K219 searches

The ordinary finite fixture collection has6,162 source-admissible
minimum-register cases. All438 native action rows are covered; independent
primitive predictions agree with2,943,996 concrete baseline transitions.
The frame relation preserves the nine logical registers and exact next
program-counter word, while allowing head translation, arbitrary sufficiently
large header gap, and arbitrary spare blocks with no reduction of their
number. This broader relation still yields only a finite search screen.

* One-common-row fold family:261 state pairs,228,636 action choices; no hit.
* Sole-incoming-state deletion:109 states,95,484 choices; no hit.
* Both actions arbitrary for the261 pairs that initially share one row:
  457,272 independently filtered first actions and10,439,790 complete action
  pairs; no hit (`whole_primitive/k219/common_both.log`).
* Both actions arbitrary for all435 pairs containing new state301 or302:
  762,120 first actions and3,623,367 complete pairs; no hit. Flipping every
  incoming write bit of the removed state gives2,777,995 complete pairs,
  also no hit. This tagged convention is one additional finite family,
  not all possible incoming-edge rewrites.
* Every single incoming row was considered for a semantically neutral
  replacement:416 rows,364,416 actions,562 finite survivors. These
  replacements are not compositional: the purported bypass often passes
  through another incoming edge of the same state. Explicitly composing
  all such rewrites for nine eligible states tested1,955 complete deletion
  tables, with no hit. Large Cartesian families for states2 and24 were
  not exhausted.
* Up to two of the previously implemented weak source rotations gave145
  layouts each for the baseline, the no-push-copy MP convention, and the
  no-push-cache convention. In each run112 layouts passed every baseline
  primitive control, and33 did not. Both one-common-row and sole-state
  screens found no saving on any passing layout. Failed baseline controls
  prevent treating an apparently correct source reassociation as a valid
  arithmetic-helper reassignment.
* The arithmetic role of the duplicate decoder13 prevents its naive
  replacement by108. Direct synthesis of both incoming actions of108,
  and separate synthesis of both arithmetic incoming actions of13 on647
  relevant CI witnesses, found no valid deletion. The two source roles
  both denote `(CD6,CC2)`, but their full counter suffixes differ.

The equality-atomic fixture collection removes observations of the40
internal primitive leaves of the four open equality macros. It retains6,104
ordinary cases and adds648 full-macro tests: every input pair5,6 in0..8,
four call sites, and two surrounding-register contexts. All438 action rows
remain covered. The finite macro contract independently requires clearing
5 and6, preserving other registers, normal return on equality, and one
break on inequality. It permits different internal equality behavior and
is therefore broader than a primitive-by-primitive screen. Files are in
`whole_primitive/k219_equality/`, with generator
`equality_macro_frames.py`. One-common-row, sole-state, and six priority
both-row tests completed without a hit. Both-row searches subsequently
completed for all 261 initially common-row pairs (10,552,196 complete
action pairs) and all 435 pairs containing state301 or302 (8,905,488
complete action pairs), with no hit.

### Several-action synthesis

`multirow_folds.c` includes the standalone core and adds a partial-execution
search over a specified set of action rows. A run stops as UNKNOWN when it
reaches an unassigned action. An action is removed from its domain only
when a finite counterexample fails before any remaining unknown action.
Domains are then combined with the same conservative partial check. Every
complete survivor must pass all frames. This is exact within the explicit
finite frames, action domain, tape range, and step bounds; it is not a
semantic proof for arbitrary register values.

The original transition assignment passes the positive control. Repeating
the two-row302 deletion reproduces the earlier domain counts162 and28,
then rejects all complete combinations. Deleting13 with all three incoming
actions8/1,38/0,42/0 arbitrary also has no survivor. Deleting108 with its
two incoming actions93/0,103/0 and one additional action13/0 or13/1
arbitrary has no survivor. Further coordinated searches are recorded in
`whole_primitive/k219/multi*.log`; only a `status=COMPLETE` receipt denotes
an exhausted specified finite family.

Compile and run, for example:

```sh
cc -O3 -std=c11 -Wno-unused-result multirow_folds.c -o multirow_folds
GENERAL_FRAMES=1 MULTI_ROWS='103 1 113 0 198 0' REMOVE_STATE=302 \
  ./multirow_folds k219.native.tm frames.bin witnesses.txt hits.txt
```

`PIN_BASE_ACTIONS=1` restricts each mutable row to its baseline action for a
positive control. `MAX_NODES` bounds optional exploration; reaching it is
reported as `BUDGET_REACHED`, never as exhaustion. `OPEN_MACROS=macros.txt`
selects atomic equality observations. The source and core both use only
the C standard library (apart from POSIX environment setup in the wrapper).

### Whole AX gate, proof refill, and the final K219 snapshot

The source has 206 distinct DAG nodes: 183 internal nodes and 23 leaf types.
One internal node has two physical representations, so the decoder has
184 roles. These counts should not be described as206 internal nodes.

The whole AX capture-gate observation spans zero-based source ordinals
4563–4596. For input selector3=c, parameter4=b, cache5=a, scratch6=7=0,
and top1=t, it clears3..7, preserves0/2/8, and clears top1 iff a=c or b=c.
The concrete reference appends3c+b spare blocks1 and increases the gap by
a+2b+4c plus t if the top is cleared. The independently checked fixture
set uses a,b,c=0..4 in three surrounding contexts:375 whole-gate frames
and6113 ordinary cases. All438 action rows remain covered. Its completed
both-row common-pair search considers261 pairs and10,169,766 complete
action pairs, with no hit. Sole-incoming deletion considers109 states and
95,484 choices, also with no hit.

The atomic refill observation spans prefix01. Inputs have NP=n≥3,
PL=selector3=scratch6=scratch7=0. It returns NP=n+1 and PL=n at prefix10,
preserving all other logical fields; with one spare1, the reference has
3n+2 spare1 blocks and extra gap2n. Fifteen fixtures sample
n=3,4,5,8,13 in three surrounding contexts. The490 prioritized both-row
pairs finish with12,682,846 complete action pairs and no hit.

The combined gate/NIP/MP/refill oracle has6646 frames:6076 ordinary,
375 whole gates,18 NIP comparisons at its actual scratch6=1,162 MP
comparisons, and15 refills. The generated binary SHA-256 is
`e50f919d12a525f7f63c84678c9fb5c26b2de8dd2c136f2d5b054948e50872cf`.
`generate_macro_frames_portable.py` reproduces that binary, the witnesses,
the prefix file, and the interval file byte for byte. Its standalone
source-invariant driver also reproduces the original facts JSON exactly.
The combined sole-incoming screen completes109 states /95,484 actions
without a hit; broader both-row searches are reflected in the snapshot.
The490 prioritized both-row combined-gate pairs subsequently finish with
12,982,524 complete action pairs and no hit. Its separate435-pair family
containing301/302 remains in progress at this snapshot.

All four disjoint-window-prioritized state-pair shards under the combined
equality/refill oracle have now completed:10,716 pairs,18,774,432 first
actions,81,693,042 complete action pairs, and no survivor. The observed
window disjointness is only a finite prioritization heuristic; this is
not an exhaustive search of all23,871 state pairs or a universal context
separation proof. The receipt is
`whole_primitive/k219_combined/disjoint_complete_receipt.json`.

Fifteen atomic-equality three-row families delete302 by varying103/1,
113/0, and one extra row. All finish without a survivor, with29,605,134
total partial-search nodes. The extra rows are113/1,97/0,97/1,4/0,4/1,
40/0,40/1,198/0,198/1,66/0,66/1,103/0,108/1,10/0,10/1.
The atomic four-row deletion of108 varying93/0,103/0,13/0,13/1 reaches
its10,000,001-node budget with no hit. It is **partial**, not exhausted.

The new incoming-movement family uses1616 oriented priority pairs whose
deleted state has a uniform incoming move direction. Reversing those
moves shifts the head at the merged role by minus twice that direction;
both retained actions are then synthesized. The cache's changed-entry
state, head, and tape were checked against complete execution. An initial
regression difference was only budget accounting: old cached execution
gave the full finite allowance after the prefix, while full execution
charged the prefix too. `COUNT_PREFIX_STEPS=1` selects the latter rule.
With equal accounting,121,536 comparisons across12 pairs agree. Legacy
completed searches used the looser cached allowance; their negative
results are not invalidated by identifying this difference.

Both incoming-displacement shards complete: 1,616 oriented pairs and
24,836,368 complete action pairs, with no survivor of the full fixture
collection. The shard action totals are 12,690,912 and 12,145,456.
Their 2,883,580,849 finite checks take 233,990,924,494 simulated steps.

A further finite discovery contract allows arbitrary final D4 only on
whole-gate inputs a<c, and on unequal MP comparison exits. Requiring
D4=0 when a≥c preserves the existing START(c=0) and reset(c=a) interfaces.
The150 gate and144 MP fixture masks are recorded explicitly. The
one-common-row and sole-incoming screens finish without a hit. A survivor
under this relaxed interface would still require an unbounded concrete
macro proof and the revised completeness/reset argument.

Formal analysis later gives the broader sufficient gate condition c>0,
while c=0 still forces D4=0. This preserves START and a universal cleanup
block that does not need to know the residual D4. Separate c-positive
fixtures relax300 gate cases and144 MP cases. Their one-common-row and
sole-incoming screens also complete without a survivor; the previous
narrower receipts remain unchanged.

The portable bundle is `portable_machine_search/` (also zipped). Its
`search_snapshot.json` records completion, budget exhaustion, and partial
progress per preserved log. It must be consulted for the still-running
combined-macro family containing states 301/302. No finite screen proves a state
lower bound, and no ≤218-state machine is claimed in this supplement.

The helper portability audit was resolved before packaging: source-rotation
helpers now detect bundled vendor/input paths, the whole-rotation driver
accepts an explicit solver path, and the mask and movement generators accept
all input/output paths on their command lines. Fresh runs reproduce all five
c-positive mask files and all three movement pair lists byte for byte. The
whole-rotation depth-zero positive controls pass all 6,162 ordinary frames.
The historical direct-entry local-window fold search in search_rotations.py
remains explicitly archival and requires the external inv_fold.py/sim_fold.py
repository modules; it is excluded from the standalone reproduction claim.
