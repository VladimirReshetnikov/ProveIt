# Supplementary research and its exact scope

The accepted result is `../machines/zfc239.tm`, proved by the main checks in
`../verification/`. None of the supplementary logical substitutions, source
specializations, or alternative layouts below is a premise of that result.
All commands in this file run from the **companion package root**. Use Python 3
with assertions enabled, without `-O` or `PYTHONOPTIMIZE`, and choose fresh
output locations to preserve the archived evidence.

## Successful discovery search

`search/` contains the C++17 search that found the three delayed-erasure
variants. It jointly chooses a shared control state and compensating helper
rows. The retained finite radius-five tape domains came from exact finite
executions. They are underapproximations used to find candidates, and are
not a reachability theorem. Acceptance of the selected `80/0 = 0 L 106`
variant uses the separate full unbounded proof.

```sh
python3 -B research/search/reproduce_discovery.py \
  --baseline reference/zfc240_old.tm --output-dir /tmp/zfc239-search
```

This compiles the supplied source with `g++`, runs the frozen domain file,
and writes three candidates, a search log, and a receipt. The recorded run
examined 28,680 state pairs and 1,318,621,440 helper-row actions in 282.27
seconds. Bounds 63 and 127 apply to old and new local blocks in discovery.
The search space restriction and complete counters are in
`search/discovery239_receipt.json`; they do not constitute a lower bound.

The independent source interval checker used to prepare these domains can
be rerun separately:

```sh
python3 -B research/search/source_intervals.py machines/sites_logical.json \
  --cap 3 --output /tmp/zfc239-intervals3
```

`frame_domains.cpp` records the exact finite domain-generation algorithm.
Its CLI is `TABLE GUARDED_SITES OUTPUT RADIUS SCENARIOS --guarded`; the frozen
run used radius 5, eight scenarios, the supplied `guarded_sites.txt`, and
the complete 409,691-transition predecessor bootstrap. It accumulated
29,131 distinct windows over 36,318,413 literal transitions.

## Logical basis compression and cost controls

`formalisms/specialization_obstructions.tex` is included as an appendix in
the main report. It gives two precise logical nonderivability results for
specializations of the fourth input of the inherited classical axiom.
The first covers every implication-only reconstruction
`U(a,b,c,Truth)` of arbitrary size; the second covers `U = not b`.

The finite matrices validate the retained seven logical rows, modus ponens,
generalization, atomic fresh vacuity, and irreflexivity. They invalidate
Peirce's law. **They are not asserted to satisfy CP or GIC**, and so do not
establish that the resulting set theories are weaker or inconsistent.
The report also discusses the separate possibility of a calibrated
intuitionistic, non-extensional theory.

The standalone checker writes its receipt beside itself. To retain the
archived receipt, copy it into a fresh directory first:

```sh
mkdir -p /tmp/zfc239-matrices
cp research/formalisms/check_specialization_obstructions.py /tmp/zfc239-matrices/
python3 -B /tmp/zfc239-matrices/check_specialization_obstructions.py
```

The main reproduction driver already performs this matrix check in its
chosen output directory.

`formalisms/controls/` contains eighteen diagnostic compiler outputs and
their full source, row counts, missing-row records, and hashes. These use
the public 281-state backend, not the optimized 240-state backend. They
retain the public backend's missing `1.inc/read1` transition. **These are
partial diagnostic programs, not new total ZFC consistency machines.**
No count difference is transferred to the 239- or 240-state machine.

To regenerate the controls, supply a checkout of ProveIt at commit
`13ec39ed43148b1807f51ed6e6528e1c84659562`:

```sh
python3 -B research/formalisms/measure_specializations.py \
  --repo /path/to/ProveIt --out /tmp/zfc239-cost-controls
```

This optional command uses the unchanged `recover_wade_dag.py`,
`theory_backend_experiment.py`, and `pairing_backend_experiment.py` helper
modules from that checkout. The pinned upstream compiler, source DAG,
logical specification, and license are supplied under
`formalisms/reference/`. See `formalisms/HANDOFF.md` for exact measurements,
source URLs, and interpretation.

## Restricted exact-step quotient obstruction

```sh
python3 -B research/permutation_quotient_screen.py \
  --table reference/zfc240_old.tm --output /tmp/zfc239-quotient.json
```

This computes the greatest exact-step transition relation after relaxing
twelve selector targets independently. The relaxed family includes every
register permutation. The resulting relation is diagonal. This excludes
that precisely defined route to an exact-step state quotient; it does
not exclude context-sensitive sharing or comparisons after multiple
steps. The successful delayed-erasure fold is outside this family.

## Source reachability and the NIP specialization

```sh
python3 -B research/reachable_intervals.py \
  --source machines/sites_logical.json --cap 8 \
  --output /tmp/zfc239-intervals8.json
```

The interval calculation establishes seed inclusion and inductive closure
on the finite source graph. It rules out five guarded cases of the exact
source and proves several register facts. The main 239-state proof still
checks all 8,386 original guards; none of these exclusions is used there.

```sh
python3 -B research/nip_specialize.py \
  --sites machines/sites_logical.json --table reference/zfc240_old.tm \
  --intervals /tmp/zfc239-intervals8.json \
  --output-dir /tmp/zfc239-nip
```

The NIP experiment reduces the source from 6,455 to 6,449 leaves. Its local
source precondition is `R6 = 0`, with arbitrary natural `R5` and arbitrary
other registers. The source certificate combines exact affine cases with
natural-number induction on a clearing loop and checks 8,369 outside
commuting edges. **The emitted binary candidate still needs its state-72
route repaired.** The script marks it `UNVERIFIED_NIP_LAYOUT_REQUIRES_72_ROUTE_REPAIR`.
The archive preserves the source certificate and source list, not an
assertion of a second smaller binary machine. This NIP strategy has prior
art; the exact current-source specialization is the result recorded here.

## An independently verified alternative 240-state layout

`cluster_variant1/` preserves a different 240-state layout with source
depth 48 rather than 51. Its source relation has 1,932 pairs. Both source
bisimulation and complete initialization have been independently replayed;
the research run also passed all 8,386 unbounded runtime cases.

```sh
python3 -B verification/verify_alternate_layout.py \
  --baseline-table reference/zfc240_old.tm \
  --baseline-sites machines/sites_logical.json \
  --alternate-dir research/cluster_variant1 \
  --output /tmp/zfc239-alternate.json
```

To include a fresh full runtime replay for this optional layout, append
`--runtime verification/symbolic_runtime.py`. The standalone verifier pins
all four inputs, recomputes the source relation, and checks the complete
blank frames. Its optional runtime mode retains the original engine rules
and baseline validator. See `cluster_variant1/README.md` for the exact
distinction between its quick and full modes.

## Interpretation and historical evidence

`source_encoding_notes.txt` is a qualified research handoff, not an
additional proof endpoint. Some original receipts retain filenames and
absolute paths from the runs that produced them. Those historical fields
identify the run; the commands above are portable. Packaging adaptations
and byte identities are recorded in `../provenance.json` and
`../MANIFEST.sha256`.

The accepted 239-state machine uses the original source unchanged. The
supplementary results document tested alternatives and useful constraints
for future reductions, with source-level, binary-level, and logical claims
kept at their demonstrated scope.
