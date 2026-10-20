# Exact K224 contextual fold research

Input: ProveIt commit `49ee7cfdc8`, authenticated `K224_Construction_2026-10-20`
packet. All scans use the exact legacy-label 224-state table with SHA-256
`e8467b9745c7a05860797a209ed05ce0b41b72a44d96f00aad43630a589ccc2f`.
The unique terminal is 254; the blank start is 95. Source SHA-256 is
`309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878`.
Intake is never modified.

## Completed result

No <=223-state candidate survived 16 completed state-reduction screens.
The additional neutral-transition screen produced 582 source-domain edits,
which are a search library rather than a state reduction.

The precise radius-6 source domain has 57,587 working-state windows; its
radius-5 projection has 28,102. All 6,233 admitted cases and 448 rows were
covered, followed by the exact 409,835-step startup. Independent literal QA
also passed 676 guard/parameter cases (1,065,991 steps including startup).

On the precise domains, all four fold families found no survivor. Caller-only
and halt-aware caller deletion each examined 223 deletions, with state 4
capped. The one-neutral-helper caller search completed 6,244 helper trials on
13 targets, with states 4 and 30 capped. The repair search tested 1,240 caller
assignments with up to three further helpers; targets 2, 4, 25 and 30 were
sampled rather than exhausted. Exact per-screen counts and hashes are in
`REPORT.json` and `SHA256SUMS`.

## Scope

Every search here is bounded candidate discovery. A survivor requires an
independent whole-tape or source-reachable unbounded runtime proof, plus
exact complete blank startup. A no-hit result is not global minimality.
The local old/new orbit match uses positive blocks of at most 65 steps in a
radius-6 window (radius 5 where the filename says `r5`).

The ordinary scans use the inherited `research_sub226/new_folds` sources.
They cover ordinary state identification, head offsets of +/-2, and an
adjacent-cell complement encoding. `offset_tag_folds.cpp` combines the last
two encodings: an incoming edge reverses its move and complements its write.
All four families vary the retained state's two rows independently, while
other rows change only as required by the encoding. Direct terminal targets
are excluded by these inherited scanners; the separate halt-aware caller
screen includes them and ignores head/tape differences at a matched halt.

## Caller-specific deletion

`incoming_elimination.cpp` deletes one state by changing every incoming row,
allowing each caller a different destination, write and move. Deleted-state
self loops disappear with the state. The retained rows need not implement a
single state identification. Optimistic partial assignments are checked
before combinations are filled, and all changed callers are checked together.
Each deletion has a 100,000 search-node / 10-second cap. The completed all-tape
run examined all 223 non-start deletions, found 43 initially feasible schemas,
capped states 4 and 30, and found no survivor.

`incoming_helpers.cpp` uses the parent's 550 radius-5 neutral alternatives,
then adds one outside neutral helper row. It completed 5,390 helper trials on
12 deletion targets with no survivor; the large states 4 and 30 were capped.
`neutral_repair_walk.cpp` samples caller assignments and repairs the first
failing trace with up to three further neutral helper rows. Its retained
radius-5 run tested 940 assignments, with no survivor. Three large assignment
families were sampled, so this is not an exhaustive negative result.

## Source-reachable domains

`precise_seed_domains.py` and `runtime_projection_common.py` adapt the precise
projector in `ZFC_Compact_Search_2026-10-20/experiments/decoder` to this exact
224 table. They use the unchanged pinned symbolic runtime engine and the
current source invariant independently checked by
`research_sub224/engine/independent_check.json`.

The current source has 4,799 primitive sites and 6,238 unrestricted guards.
The checked source invariant excludes five guard cases: positive guards at
sites 4658 and 4773, and unreachable sites 4659, 4774 and 4775. Therefore a
complete seed-relative projection must cover exactly 6,233 cases.

The projector includes literal states, every unary scan interior, arbitrary
finite-list traversal interiors, and all 409,835 exact blank-start steps.
Run lengths are saturated at twice the half-window width, retaining both
truncated consumed and remaining lengths. Register domains use exact values
0..7 and a single >=8 bucket. Independent prefix/suffix languages widen
correlations safely. The result remains a discovery aid; candidate correctness
is established by a fresh whole-runtime proof, not by the finite projection.

Atomic checkpoints are written every 100 source sites. Restart with `--resume`;
the checkpoint binds the exact table, source, invariant, projector and adapter
hashes. Diagnostic language-cache counts are segment-local after a resume;
case coverage, symbolic steps, row coverage and unioned domains are cumulative.
The earlier broad collectors were interrupted by executor loss and have no
completed output. They are not used as evidence.

`finish_precise_domains.py` validates complete coverage, removes terminal-only
contexts for scanner input, and projects radius 6 to radius 5. The automatic
`run_precise_screens.sh` runs the precise-domain fold/caller/helper families.

## Positive controls

1. `known224_fold_control.txt` recovers the exact supplied 225-to-224 fold.
   `check_known224_control.py` checks exact table equality and independently
   proves all 450 old rows on open whole tapes. The block histogram is
   446 one-step, three three-step and one five-step blocks.
2. `elimination_positive_control.txt` recovers a caller-specific bypass.
   `check_elimination_control.py` independently checks the exceptional blocks
   over all affected input bits; every other tape cell is untouched.

No new <=223-state machine is claimed unless a separate complete certificate
is subsequently added.
