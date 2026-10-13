# Candidate-selection comparisons

This package compares native `candidate_policy='subsets'` with
`candidate_policy='conflicts'` in the same fixed-source Euler oracle. Diagram
queries use `transversal_candidate_policy` with `sector_method='transversal'`.
Both arms use the default polynomial exact LP policy, source-model equations,
vertex preprocessing, and identical finite diagram-query allowances. The
native default remains `subsets`.

The theory and remaining structural hypotheses are in
`../../synthesis/conflict_candidates.tex`, `boundary_transversal.tex`, and
`euler_transversal.tex`. This package supplies finite evidence; it does not
establish a general quasi-polynomial recognition bound.

Run from `Topology/UnknotRecognition/fast`, after all pinned sources are frozen.
Use a Python environment containing Regina for the audit; the benchmark and
solver-free checker require only the native standard-library dependencies:

```sh
python -B -m conflict_candidate_research.audit --output ../synthesis/data/conflict-candidate-audit.json
python -B -S -m conflict_candidate_research.check_evidence
python -B -m conflict_candidate_research.benchmark --output ../synthesis/data/conflict-candidate-benchmark.json --pairs 5 --aa 1 --batch 1
python -B -S -m conflict_candidate_research.check_evidence --benchmark ../synthesis/data/conflict-candidate-benchmark.json
```

Reserve the CPU for the timing command. After rebuilding the article and PDF,
add `--publication` to the last command to pin the evidence, relevant tests,
all three theory sections, the main article, both READMEs and report PDF.
Publication also pins the boundary-transversal package and evidence, runs its
solver-free replay afresh, and requires its retained audit/replay/regeneration
source pins and observations to match current files. Singular and plural
`conflict-candidate*` evidence logs and the candidate-policy tests are included. The
checker also writes `synthesis/data/conflict-candidate-table.tex` from verified
samples. Generated evidence belongs outside this package.

The audit and timing files pin the full native Python package, inherited
research dependencies, the retained lower-witness fixtures, and every Python,
JSON and Markdown file in this package. Pins are checked at both ends of a
run. No historical implementation is loaded: both policies execute the same
pinned current solver and differ only in candidate selection.

## Fresh correctness comparisons

The audit performs fresh Regina **original STANDARD vertex** enumeration on
three original supplied sources. It checks all 64 masks on a two-tetrahedron
layered solid torus, plus 12 masks each on sources with an interior vertex and
multiple boundary vertices. These 88 masks run under both candidate policies
and both envelope-first and anchor-only strategies: 352 complete supplied
queries. Supplied-query allowances are unbounded. Incompatible masks are
intentional; the original STANDARD oracle is filtered independently by each
mask's allowed Q coordinates and positive nonlink Euler characteristic.

Every positive answer is checked against original incidences, then undergoes
full-source extreme-ray extraction. Its support must decrease, its primitive
coordinates must appear in the fresh original STANDARD list, and its native
crushing quotient must equal Regina's quotient with the exact retained labels.
Every negative answer supplies a complete independently replayed Euler tree.

Fresh diagram queries cover the crossing-free circle, the trefoil braid
`(2; 1,1,1)` and the figure-eight braid `(3; 1,-2,1,-2)` under both policies.
Full recognition certificates and every labelled crushing quotient are
retained. A finite cap produces an explicitly saved `INCONCLUSIVE` result and
verified partial chain, never a negative result or an exact-transversal claim.

The existing 19 formal positive root-ray fixtures are replayed separately for
each applicable policy endpoint. These are retained discoveries, not fresh or
exhaustive root-ray enumeration. Original matching, canonical minima, formal
positive Euler characteristic, primitive Q coordinates and Q support nullity
one are independently verified. Incompatible vectors are formal coordinates,
not embedded normal surfaces. Disjoint full conflict sets give a lower bound
for the labelled source; the new complete negative tree's union of split
tetrahedra gives an equal upper bound. Exact source equality is mandatory.

The solver-free checker runs with `python -S` and imports no Regina. It reuses
the prior independent geometric checker on a supplied-only, policy-neutral
view of each arm: masks, original oracle coordinates, extracted rays and saved
negative/crushing proofs are unchanged. This package directly checks arm names,
configurations, candidate metadata, diagram chains and finite transversal
bounds. Completeness of the saved STANDARD lists remains evidence from the
fresh Regina enumeration; replay checks every listed ray and every comparison.

## Paired timings and counters

Each timed query includes native exterior construction, shelling, vertex
preprocessing, candidate filtering, failed candidates and depth restarts, all
LP work, internal proof replay, and full-result serialization. Imports,
prepared diagram objects, and separate independent warmup verification are
excluded. Five paired samples use a fixed shuffled order, with one shuffled
`subsets`/`subsets` A/A pair per case. Full warmup proofs are retained, and every
timed serialized result must have the verified warmup's exact digest. The
checker additionally requires warmup results to equal the separate audit's
results for the same policy and configuration.

Both arms must complete the expected recognition before timing can pass.
Unexpected bounded partial outcomes are retained with `passed=false` and are
not reported as a comparison between completed recognitions. The checker
reconstructs shuffle order, elapsed-time arithmetic, medians and paired ratios.
Raw work statistics accompany every warmup and timing sample.

`hitting_subsets_tested` has different operational meanings: the subset policy
counts candidate subsets, including cached-edge filtering; the conflict policy
counts visited partial candidate-search states, including repeated roots at
new depth allowances. Compare actual `transversal_candidates`, restarts,
oracle nodes, LP pivots, anchors, ellipsoid updates and feasibility decisions
alongside this count. `learned_conflicts` counts insertions, including relearning
a forgotten edge. Only the conflict policy limits its FIFO cache to 256 entries;
cache peaks and evictions are recorded. These finite measurements supply no
universal bound on either the minimum transversal size or conflict size.
