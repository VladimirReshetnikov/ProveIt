SOURCE-CONDITIONED CONTEXT RESEARCH

This subdirectory preserves two complete U208 context harvests, five completed
bounded discovery screens, their code, exact inputs, and explicit dependencies.
No screen here found an accepted 207-state machine. The independently completed
two-row screen using the stronger contexts is in research/two_row.

FAST PORTABLE CHECK
  python3 -B research/source_contexts/replay.py
  python3 -B -O research/source_contexts/replay.py

These commands verify exact data/dependency hashes and recorded censuses. They
do not pretend to rederive a universal runtime or rerun an expensive search.

OPTIONAL FRESH REPLAY (from the delivery root)
  python3 -B research/source_contexts/replay.py --action harvest --output /tmp/unrestricted_contexts.json
  python3 -B research/source_contexts/replay.py --action restricted-harvest --output /tmp/restricted_contexts.json
  python3 -B research/source_contexts/replay.py --action aliases --contexts restricted --depth 12 --limit 71 --include-initial --output /tmp/restricted_aliases.json
  python3 -B research/source_contexts/replay.py --action folds --contexts unrestricted --depth 10 --limit 45 --output /tmp/source_folds.json

Harvest actions require enabled assertions and may take several minutes. The
wrapper extracts the hash-bound Entry Context archive into a temporary staging
tree with the original experiment paths. It copies the retained interval facts
into that tree and runs the original code there. It writes experiment results
only to the explicitly chosen output. Standard-library Python 3.10+ is sufficient.

COMPLETE RUNS AND SCOPE
1. Unrestricted harvest: 5,084 guarded arbitrary-natural contracts, 1,251,865
   symbolic inferences, all 416 literal rows, 48,140 literal startup steps.
   Radius 4 produces 21,358 windows. Unary/list entry states were deliberately
   widened to all local windows, conservatively losing some useful information.
2. Direct aliases: 42,642 directed pairs, bound 31, no survivor.
3. One-row mutations: 448 compatible oriented pairs, 370,944 mutations, bound 31,
   no survivor. Helper equal to keeper is included; removed state is excluded.
4. Repeats of 2/3 intersected with depth 10 history, bound 45: still no survivor.
5. Restricted harvest: 5,079 admissible contracts, 1,243,924 symbolic inferences,
   all 416 rows and 48,140 startup steps. Source interval/branch facts and the
   inductive all-spares-one property are used; primary register magnitudes and
   gap remain unbounded where allowed. Remaining spare-list length is arbitrary,
   represented by its symbolic width, a nonnegative multiple of 3. Fixed-value
   one-block lemmas are rederived literally. Precise unary-loop interior windows
   replace the previous full widening. Radius 4 gives 12,490 windows.
6. Restricted direct aliases: 42,849 directed pairs including keeper 0, depth 12
   history intersection, bound 71, 51,279 disjunctive cylinders, no survivor.

Two duplicate attempts at a restricted one-row depth 12 screen did not produce
a final receipt after executor sessions became unavailable. No completed
negative result is claimed for those attempts. The main report instead uses
the completed broader two-row screen recorded separately.

DISCOVERY IS NOT ACCEPTANCE
The contexts are generated for searching. Finite random completions reject
candidates; every accepted local candidate would still need complete symbolic
branch checking and then a fresh candidate runtime/startup proof or a complete
reachable-context simulation theorem. A rejected sampled case may lie in an
overapproximation rather than the actual blank run. None of these negative
results is a lower bound for consistency machines.

The source interval facts were produced and checked by research/logic. Their
exact bytes are retained here for reproducibility. This module does not claim
to rederive them in its fast dependency check. The all-spares-one invariant
starts from 43 spare registers of value 1; CI appends 1 and the other canonical
primitive contracts preserve the list. No finite spare-list sample substitutes
for the list-induction lemmas.

The compression helper was optimized after the recorded searches: integer-mask
subsumption preserves the same ordered cylinder union as direct finite-set
inclusion. The discovery code's semantic candidate family is unchanged. Paths
inside original receipts identify the original working tree; DEPENDENCIES.json
and replay.py supply the portable dependency reconstruction.

FILES
  data/             Complete harvested windows; selected compressed cylinder
                    families; restricted case-duration census; harvest logs.
  receipts/         Completed search receipts/logs and fresh primary runtime.
  facts/            Exact independently checked source-interval input.
  original_code/    Exact experiment code at archival preparation.
  DEPENDENCIES.json Exact hashes, original paths, upstream ZIP identity, scope.
  replay.py         Portable staging/check/execution entry point.

Attribution: the source/table/runtime/discovery infrastructure comes from the
supplied Entry Context packet and its retained lineage. The instrumented window
harvest, bounded scan projection, context intersections and packaging were
prepared during this analysis. Original archive notices remain attached to the
retained baseline ZIP and baseline/snapshots/notices.
