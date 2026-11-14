# Source-conditioned reductions and offset quotients

These experiments produced **no accepted machine below 196 states**. The negative
results concern explicit bounded synthesis templates; they are not a lower bound
on the state complexity of a consistency machine.

## Inputs

The baseline is James Chang's PA196 at commit
`407cdc356f6b586635e71ac92be394255f4bfea4`, literal table SHA-256
`e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8`.
The ProveIt archive snapshot used in this session is
`dc523e7b06ffb414093c90aa035500ca283e5f75`.

The historical native-state conventions in the inherited runtime are retained.
See the files in `inputs/provenance/` and the upstream licenses. In particular,
this package does not relicense inherited code or suggest upstream endorsement.
The inherited source-context collector and C++ two-row screen came from
`docs/incoming/pa196_research_2026-11-13.zip`. The two archived alternative tables
came from `docs/incoming/pa_tm_comparison_and_reductions.zip`, directory
`rotated196/`. `scanner15` is a source-CFG-preserving layout developed during this
session by a separate comparison task; its supplied complete-frame/startup receipt
is retained. It has 196 states.

## New completed screens

1. **Wider local simulation.** The unchanged PA196 source has 4,959 branch
   contracts. The collector projects a source-conditioned enclosure to nine tape
   cells (four on either side of the head), producing 12,168 admitted
   control/window pairs. It intersects that enclosure with the independent
   radius-six blank-window closure. The synthesis permits positive child blocks
   of at most 32 steps, one ordered state identification, and two arbitrary
   changed rows of retained states. Every endpoint must have the parent's
   projected control, head position, and all nine tape cells exactly.
   All 38,220 ordered folds were screened. There were 174,570,928 first-row action
   trials and 1,866,384,912 second-row action trials; 803 passed the representative
   prefilter and none passed all obligations. Counts are not counts of distinct
   machines, because one machine can have multiple presentations in this search.

2. **Third-row repairs of prior near misses.** Within the inherited five-cell,
   16-step template, the 633 two-row representative passes were additionally
   tested with one arbitrary third changed row. The possible third row must lie
   on each remaining failed trace. There were 1,400 candidate third keys and
   1,097,600 third-row action trials; none succeeded. This is deliberately a
   limited third-row search. It does not cover candidates whose first two repairs
   fail the representative prefilter.

3. **Previously accepted alternative layouts.** Fresh symbolic contexts and
   exact startup checks were generated for `rotated196` and `rotated196-macro62`.
   Both have 4,959 complete primitive contracts and reach the same full candidate-2
   seed after 58,294 steps. Their five-cell enclosures have 2,223 and 2,217 windows.
   Separate exhaustive two-arbitrary-row screens produced no survivor.

4. **Head-offset quotients.** A removed control can be represented by a retained
   control two cells behind its old head. When all incoming transitions have
   direction d, use offset -2d and flip the direction on every redirect into the
   removed control. This is a different template from an equal-head state fold.
   All 33,345 uniform-incoming ordered pairs failed without an extra repair.
   Allowing one arbitrary retained-row repair tested 44,853 eligible keys and
   35,164,752 actions, again with no survivor. The remaining 4,875 mixed-direction
   pairs were also screened using a relation indexed by the incoming direction;
   246,176 single-helper actions produced no survivor. These offset screens use
   nine cells and at most 64 steps.

5. **Two-row offset repair.** The baseline uniform-incoming offset template
   was also checked with two arbitrary retained-row repairs. All 33,345 ordered
   pairs were covered, with 179,423,888 first-row and 14,854,027,776 second-row
   action trials. None survived. This remains a bounded nine-cell, 64-step
   template, not an unrestricted impossibility result.

6. **Global source and spare invariants for the new diagonal196.** The new
   logical emitter's 3,700-site source has a separately audited trit fixed point
   of 4,319,427 site/vector pairs and 4,848,294 edges. Its explicit halt site is
   still abstractly reachable. Exact affine marginal cases and the invariant
   that every spare block has value one reduce the five-cell enclosure from
   2,210 to 2,173 windows, and the nine-cell enclosure from 11,962 to 10,749.
   All 5,149 restricted affine cases pass, together with the full 58,154-step
   blank startup. The five-cell two-row screen checks all 38,220 ordered folds
   and has no survivor. Its 627 representative near misses were also checked
   with 1,097,600 third-row action trials, with no survivor. Uniform head-offset
   zero/one-row repair is also negative on the refined contexts. See
   `TRIT_CONTEXTS.md`, the independent review receipt, and the exact raw counts
   under `trit_diagonal196/` for the completed scope of each screen.

7. **Completed refined wide and closing screens.** On the new diagonal196,
   the nine-cell,32-step two-row screen checks all38,220 ordered folds:
   174,648,544 first-row actions,1,904,561,008 second-row actions,797 representative
   passes, and no survivor. The nine-cell,64-step uniform-offset one-row screen
   checks33,345 pairs and35,668,864 actions with no survivor. Four zero-closing
   variants have2,181-window differential enclosures, each supported by69 new
   affine cases plus the unchanged base cases and exact startup. Their separate
   five-cell,16-step,two-row screens each cover38,220 pairs with no survivor.
   The complete structured counts and finite budgets are in
   `trit_search_results.json`.

8. **A literal195-state shortened-scanner candidate, unproved.** The candidate
   in `scanner195/` has195 working states and390 rows. It is not an accepted
   consistency machine. Its unrestricted primitive checker fails96 obligations,
   and the source-reachable trit/one-spare refinement already fails at site0.
   A separate concrete clean-seed test has a first root return after118 steps
   whose tape differs from the required successor frame in43 cells. These are
   implementation-contract failures. They do not establish anything decisive
   about the candidate's actual blank-run consistency property. The exact table,
   failed obligations, audited separate-source trit invariant, concrete frame
   witness, and source-bound `check_scanner195.py` reproduction are supplied.

The text receipts are the authoritative raw run counts. Any additional screen
included with a receipt must be described at its actual completed scope; an empty
result file by itself is not evidence that an interrupted screen finished.

## Why an offset quotient would preserve halting

Let q be the removed state and p the retained state. Relate parent and child
configurations by identical tapes. Outside q their heads and states agree. At q,
the child state is p and its head is shifted by -2d, where d is the direction of
the transition that entered q. A parent transition entering q writes at the old
head and moves d; flipping its direction in the child puts the child head at the
required shifted location. Its tape write is unchanged.

The finite local checker verifies positive child blocks for configurations in q
and every additional modified helper state. All other parent transitions are
simulated in one step by construction. An induction on parent steps then gives
complete finite execution segments. Positive segment lengths prevent an infinite
parent run from collapsing to a finite child run, and no checked segment passes
through a halt before its endpoint. This would give equivalent blank-tape halting
once the admitted windows were justified. An initial-state deletion is handled by
translation invariance of an all-blank tape.

For mixed incoming directions the same relation allows the two offsets and
remembers which incoming direction supplies the current instance. The checker
conservatively tests every admitted q-window at both offsets. This can reject a
valid candidate that needs a more precise direction-conditioned invariant.

## Evidence status

The source collectors use executable affine-run/list induction checkers and
unchanged register-engine lemmas. They are not new Lean kernel certificates.
The earlier collectors cover arbitrary natural gaps and register contents
under the documented macro contracts; the trit refinements restrict that domain
to a proved reachable overapproximation; ordinary bounded blank runs alone do not establish that fact.
The additional fast collector conservatively uses the independent blank-window
closure for every control in the boxed engine routines.

The offset positive control is a separate six-state machine. On all 512 nine-cell
windows at every state it has the expected fold deleting state 3, retaining state
4, and shifting the removed state's head by -2. The raw control output and an
independent Python replay are supplied. This tests the nontrivial offset handling;
it does not certify the exhaustive PA196 negatives.

## Reproduction

Python 3 and a C++17 compiler suffice. Assertions must stay enabled.
`python3 reproduce.py` checks digests and replays the synthetic positive controls.
`python3 reproduce.py --full` additionally regenerates contexts and reruns the
completed exhaustive screens. The latter is computational research and can take
many minutes. The scripts emit receipts with elapsed times, which need not match
those retained here. All numerical synthesis counts refer to the exact command
and template used, not a universal lower bound.

### Reproducing the global invariant experiments

`python3 reproduce_trit.py` independently reconstructs the source CFG in three
ways, reruns the finite fixed point and its separate closure audit, checks the
exact seed and graph/bitset digests, and binds every saved context receipt to
its machine and source. `python3 reproduce_trit.py --full` additionally
regenerates the affine contexts and reruns the recorded bounded screens. The
full mode requires NumPy in addition to Python3 and a C++17 compiler. The closing-variant differential wrapper also rebuilds all four additional
source graphs and closures, and rechecks every base primitive case to identify
all affected source sites. The
collectors themselves also enforce the source-CFG and bitset digest chain to
the audited closure receipt. The default reproduction gate was run successfully
on this assembled portable bundle; the optional long screens were executed
individually with the supplied sources and inputs.

The supplied diagonal tables are196-state machine implementations. These
engine experiments do not independently prove the new emitter's arithmetic
completeness or a PA-internal consistency equivalence; those obligations are
addressed separately in the accompanying mathematical report.

`python3 check_scanner195.py` independently reconstructs the exact unproved195
candidate and reproduces its documented implementation-contract failures. It
is a rejected verification attempt, not a positive consistency certificate.
