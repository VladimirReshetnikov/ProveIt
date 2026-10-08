# Output-sensitive two-meridian seed search

This follow-up changes the search inside the maintained optional
`fastunknot.two_meridian` stage. Its representation arithmetic, certificate
schema, independent search-free replay, public options and default pipeline
dispatch are preserved. A failed exhaustive search certifies only failure of
the specific diagram to admit the implemented one- or two-seed derivation.
It remains `INCONCLUSIVE` for knot recognition.

The original source is frozen in `baseline_two_meridian.py` from repository
commit `2b93767bd3cf7ea7c1995acd66f50c72858a30c5`, with SHA256
`5eb36230e9b9114df0f42c089ab716bfd6473ba4baf1621182170ef1a30e7b0d`.
It is loaded under a distinct `fastunknot` module name so that its relative
imports use the same unchanged dependencies as the maintained implementation.

## Three exact changes

1. **Reusable closure state.** Two generation arrays replace the old fresh
   array of rule counters for every seed set. An enqueue stamp records which
   arcs have been reached, and a dequeue stamp records which dependencies
   have been processed. Keeping these two notions separate preserves the
   original deterministic queue order and exact derivation trace. Each trial
   touches only reached vertices and incident rules.

2. **Productive prerequisite pairs.** A productive unary rule has identical
   dependencies and a different target. In its absence, all singleton
   closures are trivial. On more than two arcs, any successful seed pair
   must enable a first rule whose distinct dependencies are exactly those
   seeds and whose target is new. Thus at most one pair per rule needs a
   closure computation. The sole pair on a two-arc universe is retained
   separately because it already contains every arc. If a productive unary
   rule exists, the implementation keeps the complete old lexicographic
   pair enumeration, using the faster stamped closure engine.

3. **Pruning by proper closed sets.** If a trial exhausts its queue in a
   proper closed set C, the closure of every seed set contained in C lies in
   C. Candidate edges with both endpoints in C can therefore be skipped.
   The implementation scans only the sparse candidate graph at reached
   vertices and marks later edges. It never allocates a dense pair table or
   stores an unbounded cache of failed closures.

All omitted pairs are proved unsuccessful. Consequently the first successful
pair is unchanged, and the generation engine produces the same derivation
trace as the old counter engine. Successful certificates are byte-identical
on the frozen corpus, including all arithmetic and phase data.

## Precise search bounds

Let v be the number of Wirtinger arcs and m the number of directed crossing
rules (twice the number of crossings). For an examined seed set S, let p(S)
count dequeued vertices and i(S) count visited rule incidences.

The generation arrays cost O(v) once. A closure trial costs
O(1 + p(S) + i(S)); it does not scan untouched arcs or rules. The candidate
graph has at most m edges, costs O(v + m log(m+1)) to construct and sort, and
occupies O(v+m) words. On an unsuccessful closure, the number of candidate
incidences inspected for pruning is bounded by its rule incidences: each
candidate edge comes from an original rule with the same two dependencies.
Therefore filtered seed search costs

    O(v + m log(m+1) + sum_S (1 + p(S) + i(S)))

over the actually examined singleton and candidate-pair trials. The singleton
phase costs O(v+m) in the trivial-singleton regime; there are at most m pair
trials. For a knot diagram with c crossings, v,m = O(c), and the resulting
worst-case search bound is O(c^2) word operations, or O(c^2 log(c+2)) with
elementary logarithmic-bit index accounting. This replaces the previous
O(c^3) closure-search word bound on the structurally checked regime.

When productive unary rules are present, the all-pairs fallback keeps
O(v^2) enumeration and the same output-sensitive sum over trials. Its
worst-case bound is O(v^2(v+m)), with O(v+m) memory. No improvement for this
worst case is claimed here.

These are **seed-search** bounds. They exclude integer representation
evaluation, gcd/phase calculation, input construction outside the stage and
the mandatory certificate replay; those parts are unchanged. In particular,
this follow-up does not prove a general quasipolynomial algorithm for all
unknot diagrams or a new bound for the full fallback pipeline.

The work ledger remains cooperative. Generation initialization, candidate
construction and sorting, every examined or skipped candidate, closure
events, pruning, certificate construction and replay all use the same local
budget and caller cancellation callback. The attempt cap counts actual
closure trials, including singletons; pairs already proved impossible do not
consume a trial. It may therefore resolve a class query under caps where the
previous implementation exhausted its allowance.

## Validation

Run from `Topology/UnknotRecognition/fast`:

```sh
python -B -m unittest discover -s tests -p 'test_two_meridian*.py' -v
```

The original eight test methods remain unchanged. The six new methods cover:

- All 4,096 systems formed from the twelve distinct-arc crossing types on
  four arcs.
- All 512 systems formed from the nine crossing types with distinct under
  arcs on three arcs, including productive unary rules.
- Empty and one-/two-arc cases, plus 400 seeded random degenerate systems.
- An independent repeated fixed-point computation, exact old/new queue
  traces, candidate completeness, closed-set pruning and the first successful
  seed, for every singleton and pair in each such system.
- Full uncapped old/new stage comparison on the twenty previously published
  natural fixtures, with identical certificates and outcomes.
- Planar one-seed/unary-active fallback inputs, strict shared-work boundaries,
  global cancellation and certificate replay with the search disabled.

These exhaustive small-rule tests check the search combinatorics, not the
realizability of every abstract rule system as a knot diagram. The separate
natural fixture and existing planar/arithmetic tests retain that distinction.

## Reproducing the measurements

```sh
python -B benchmark_two_meridian_search.py \
  --rounds 9 --pipeline-rounds 5 \
  --output results/two_meridian_search_20261008.json
```

`corpus.json` extracts the twenty inputs and their already established labels
from `results/two_meridian_20261008.json`, with original source hash and commit.
No benchmark fixture is synthesized to favor the new candidate graph.

Standalone arms comprise the frozen baseline twice (A/A), stamped closures
without candidate filtering, candidate filtering without closed-set pruning,
and the complete maintained change. Each fresh stage invocation includes PD
validation, exhaustive seed search, arithmetic and replay. Exhaustive failure
is a completed **class query**, explicitly distinguished from a conclusive
knot verdict. A separate work-capped probe retains the old two-million-unit
and 10,000-trial bounds.

Whole-pipeline arms comprise the frozen old stage twice (A/A), the optimized
stage, and the stage disabled, all under the same maintained recognizer.
Ordinary and compressed-group configurations retain the previous filters,
replay and fallbacks. The 50-millisecond stage deadline remains unchanged.
Pipeline `UNKNOWN` results are retained and excluded from completed-time
medians and paired speedups. Arm order is seeded and shuffled; one warmup is
excluded for every case/mode/arm. The JSON records all samples, unique
certificates, source hashes, exact configurations and completion counts.

Source hashing freezes the actually imported `fastunknot` dependencies, the
benchmark, the extracted corpus, the frozen baseline and the exact compiled
ablation sources. Unrelated unimported research modules can be edited without
changing the experiment. Imports and corpus loading are outside timers.

### Recorded results

The checked run is `../results/two_meridian_search_20261008.json`. All 900
measured standalone calls completed their exhaustive class query. Sixteen of
the twenty fixtures have conclusive knot verdicts; survivor-01, Gordian,
Conway and Kinoshita--Terasaka complete only the class nonmembership query.
Every conclusive result retains the exact frozen certificate.

| Fixture | Old/new trials | Old/new work | Old/new standalone median (ms) | Paired speedup |
| --- | ---: | ---: | ---: | ---: |
| Gordian | 10011 / 274 | 4347002 / 12251 | 297.346 / 3.460 | 85.861 |
| survivor-01 | 120 / 23 | 7071 / 898 | 0.882 / 0.295 | 3.001 |
| survivor-00 | 60 / 23 | 5175 / 2286 | 0.873 / 0.593 | 1.319 |
| Conway | 66 / 19 | 3115 / 731 | 0.438 / 0.236 | 1.790 |
| Kinoshita--Terasaka | 66 / 19 | 3115 / 729 | 0.449 / 0.238 | 2.028 |

Speedups are medians of matched per-round ratios, not ratios of the displayed
medians. The Gordian A/A ratio is 0.991. Its candidate graph contains 274
edges; 141 later edges are excluded by proper closed sets, leaving 133 pair
trials plus 141 singleton trials. The maximum closure size is five. The old
two-million-unit capped probe does not exhaust the seed class, while the new
probe does. This does not determine the knot type; the fixture was already
known to be an unknot independently.

Whole-pipeline measurements contain 800 measured calls plus 160 warmups.
Of those measured calls, 780 complete and agree with the old labels; the
twenty ordinary-configuration Gordian calls are censored `UNKNOWN` results.
The survivor-00 paired full-query speedups are 1.221 (ordinary) and 1.245
(compressed group). The group-enabled Gordian paired speedup is 1.034, with
fallback-dominated baseline/optimized medians 1.338/1.375 seconds. These
different medians and paired ratio coexist because the latter is computed
round by round. They do not justify a substantial full-recognition speedup.

The optimization also incurs small regressions on some fixtures. For example,
the ordinary survivor-04, mirror-08 and survivor-09 paired ratios are 0.822,
0.824 and 0.794. A/A variation is material for these millisecond-scale
measurements, including a group-configuration ratio of 0.820 on survivor-03.
The raw results retain all of these cases. No claim is made of an across-the-
board full-pipeline improvement or of an unbiased population-level effect.

## Further questions

- Characterize the diagram families for which productive prerequisite pairs
  have uniformly small closures; those families admit sharper output-sensitive
  bounds than the quadratic worst case.
- Replace full pair enumeration in the productive-unary regime by a checked
  quotient or singleton-closure interface, without changing which original
  seed pairs generate. Naively replacing a seed by a one-way derived arc is
  unsound because derivability need not be reversible.
- Produce a compact, independently checked proof of exhaustive two-seed
  failure from a cover of the candidate graph by proper closed sets. Such a
  proof certifies a diagram-class property, not knottedness.
- Determine whether using an early first-pair probe avoids candidate-graph
  construction on easy positive inputs without harming difficult cases.
- Measure when the optimized stage should be attempted relative to cheap
  simplification and invariant filters, using held-out diagrams and explicit
  timeout censoring.
- Study transformations that enlarge the two-seed-derivable class while
  retaining original meridian provenance and a bounded replayable proof.
  Their search length, not merely one closure computation, remains a major
  complexity obligation.
