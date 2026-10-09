# Pachner trace search and exact LP witness reuse

Research continuation for ProveIt, 9 October 2026.

**Start with [the research article](article/article.pdf).** Its complete TeX
sources, bibliography, tables and figures are under `article/`. The report
contains full proofs, implementation details, raw-evidence references, a
claim/assumption ledger, and fifteen proposed research questions.

Pinned source revision:

`66098968e88bba797143ac1bf7ad0ac4c5f697df`

Repository:
<https://github.com/VladimirReshetnikov/ProveIt/tree/66098968e88bba797143ac1bf7ad0ac4c5f697df/Topology/UnknotRecognition>

## Main results and their scope

For the repository's generalized face-paired triangulations and formal
relative-boundary 2–3 / 3–2 replacements:

- Every finite trace with at most **U total 2–3 moves** has a constant-alphabet
  commitment encoding of length at most `3t + 5U`. There are at most
  `11^(3t+5U)` commuting trace classes, including finite prefixes.
- Exact sleep-set exploration covers those classes while avoiding redundant
  orders of independent moves. Independence concerns simultaneously enabled
  geometric events with disjoint consumed incarnations.
- If the consumed original cells lie in an allowed region of size at most `r`
  and at most `c` connected components, exhaustive search costs
  `t^c * 2^O(r+U) * poly(t+U+B)`, including endpoint testing when a complete
  polynomial predicate is available. Otherwise add the chosen predicate cost.
- Thus `c = O(log t)` and `r+U = O(log² t)` define a constructive
  quasi-polynomial search class. **No theorem here proves that all unknots
  have such a successful region. This package is not a general
  quasi-polynomial unknot recognizer.**
- Exact positive-kernel witnesses omit redundant deletion LPs without
  changing any completed certificate of the fixed deterministic propagation
  baseline. The local screening bound holds even with global cache capacity 0.
- A fully specified **algebraic control**, with no claimed triangulation
  realization, has exact LP-call counts `3s²+2s+1` versus `2s+1` and exact
  Bland-pivot counts `6s³+3s²+s` versus `3s²+s`.

Binary cocycle values grow by at most `U+O(1)` bits above their initial bound.
The locality definition uses a **cover** of the initial consumption footprint:
the actual consumed subset need not have as few components as its cover.
Maximum excess triangulation size and the number of upward bursts are not
substitutes for the total-upward parameter.

## Implementation

Five new runtime modules are under `repro/fast/fastunknot/`:

| Module | Purpose |
|---|---|
| `pachner_commitments.py` | Naive, commitment, and exact sleep-set search |
| `pachner_commitments_verify.py` | Independent source-bound endpoint replay |
| `pachner_regions.py` | Canonical-parent region enumeration and aggregate search |
| `normal_pachner_search.py` | Optional diagram-to-exterior-to-disc adapter |
| `normal_propagation_cached.py` | Exact positive-witness deletion-LP screening |

All 724 files in the pinned maintained `fast/` tree preserve their bytes.
The integration layer adds 53 dependency files from the three incoming
archives and 38 files from this continuation (runtime modules, tests,
research drivers, documentation and evidence). The origins of all 91
additions are explicit in `integration/manifest.json`.

The source adapter returns `UNKNOT` only after the unchanged independent
`diagram-transport-disc-v1` checker accepts the complete proof. Bounded
family exhaustion is mapped to `INCONCLUSIVE`. The LP producer's
positive/negative statuses concern the stated positive-Euler normal-surface
query and are not unauthenticated knot-diagram verdicts.

## Recorded evidence

| Check | Result |
|---|---|
| Complete regression inventory | **1,437 tests / 181 modules; zero failures, errors or skips** |
| Small geometric comparisons | 11 cases, 34 calls, no endpoint mismatch |
| Saved geometric audit replay | 91 certificates accepted; 90 mutations rejected |
| Saved geometric benchmark replay | 126 certificates accepted |
| External Regina move audit | 23 states, 176 replacements, zero mismatch |
| Region integration audit | 5 cases, 120 literal-region searches, 302 endpoint replays |
| Diagram adapter audit | 9 calls; 4 valid positives on 2 sources; 3 wrong-source rejections |
| LP paired audit | 15 cases, 45 pairs; 36 completed certificate-equal pairs |
| Separate LP verifier-only replay | 7 distinct genuine certificates, 42 sample digest references |

On the six-independent-region genuine solid-torus control, visited trace
nodes fall from 1,957 to 64 and the median paired time ratio is **22.18**.
On the branching solid torus, LP calls fall from 41 to 22 and the ratio of
median elapsed times is **1.85**. The algebraic `s=8` control has a measured
ratio of **15.29**, reported separately.

The small geometric and LP controls include regressions. The figure-eight
LP controls remain inconclusive at 600 pivots and get no deletion-query
benefit. The literal commitment method has substantial assignment overhead.
The four diagram-adapter positives all have zero Pachner moves; they check
provenance integration rather than new move-search coverage. The empty-region
search misses a known cancelled-braid unknot. All these outcomes are retained.

Timings used Python 3.12.14 in a shared environment without CPU isolation.
Regina 7.4 was used for optional topology controls. Geometric timing ratios
are medians of within-pair ratios; LP ratios divide arm medians. There are
three recorded pairs per case, so no narrow statistical confidence claim
is made.

## Verify and replay

From this archive root, first verify the original shipped files:

~~~bash
python scripts/verify_manifest.py
~~~

From `repro/fast/`, replay the saved certificates without rerunning search:

~~~bash
python -m commitment_research.run replay \
  --input commitment_research/results/audit.json \
  --output commitment_research/results/reproduced_audit_replay.json
python -m commitment_research.run replay \
  --input commitment_research/results/benchmark.json \
  --output commitment_research/results/reproduced_benchmark_replay.json
python -m region_research.audit \
  --replay region_research/results/audit.json \
  --output region_research/results/reproduced_replay.json
python -m lp_cache_research.replay \
  --output lp_cache_research/reproduced_replay.json
~~~

The LP replay excludes capped and synthetic cases from geometric certificate
replay and imports no producer, LP solver, or native constructor.

Run the 29 newly added tests from `repro/fast/`:

~~~bash
python -m unittest \
  tests.test_pachner_commitments \
  tests.test_pachner_regions \
  tests.test_normal_pachner_search \
  tests.test_normal_propagation_cached -v
~~~

From the archive root, inspect or rerun the complete recorded partition:

~~~bash
python scripts/rerun_regression.py
python scripts/rerun_regression.py --run
~~~

The second command writes fresh logs under `reproduced/regression/`.
Regina is optional for the producer and most tests; reproducing the recorded
zero-skip native checks requires it. The historical companion directories
under `repro/reports/` and `repro/synthesis/` are required by inherited tests.

The final regression gate uses six fresh interpreters. It preserves the
earlier interrupted discovery run, the restoration of 19 pinned companion
files, and one corrected new test that had incorrectly assumed native
simplification would reproduce a frozen combinatorial triangulation.
The final selected batches all match the final test-source hashes.

## Repeat measurements

From `repro/fast/`:

~~~bash
python -m commitment_research.run audit \
  --output commitment_research/results/reproduced_audit.json
python -m commitment_research.run benchmark --repeats 3 \
  --output commitment_research/results/reproduced_benchmark.json
python -m region_research.audit \
  --output region_research/results/reproduced_audit.json
python -m lp_cache_research.audit --rounds 3 --timeout 35 \
  --figure-pivots 600 --output lp_cache_research/reproduced_results.json
~~~

Each research directory has its own README with fixture and cap details.
Fresh Regina simplification can produce a different triangulation of the
same manifold. Every baseline/screened pair still uses exactly the same
source, and saved sources can be replayed without reconstructing them.

## Integrate the additions

First review, then create the missing files:

~~~bash
python integration/apply_overlay.py --repo /path/to/ProveIt --check
python integration/apply_overlay.py --repo /path/to/ProveIt --apply
~~~

The tool verifies all prerequisite and overlay-source hashes before writing.
It accepts existing byte-identical additions and refuses conflicting
content. In a Git checkout it requires the pinned base revision; a
non-Git source snapshot must still satisfy every prerequisite digest.
The operation is idempotent while those conditions remain true. After a
new commit changes `HEAD`, the strict revision check intentionally requires
fresh review. A later repository revision should be integrated manually
after checking API compatibility rather than bypassing a failed digest.

`integration/python_changes.patch` is a review aid for 66 additive Python
files, including dependency code and research drivers. The overlays and
manifest are authoritative and also carry required fixtures and evidence.
No existing recognition default is changed and no GitHub update is pushed.

Application assumes stable source files and parent directories. It is
not transactional: an interrupted new-file write can require inspection
before retry. The optional `--output` report must be a new file outside the
target checkout and this bundle.

## Build the article

After checking the shipped manifest, regenerate tables and plots and compile:

~~~bash
python scripts/build_evidence.py
latexmk -pdf -interaction=nonstopmode -halt-on-error -cd article/article.tex
~~~

Matplotlib is needed for figure regeneration; the normal LaTeX packages
listed in `article/article.tex` are needed for compilation. CSVs preserve
the numeric values independently of the rendered tables. A rebuild may
change PDF metadata or engine-dependent bytes; the manifest authenticates
the original shipped files.

## Further research

The report develops fifteen questions with concrete intermediate goals.
The main priorities are a uniform small-region coverage theorem (or a
rigorous counterexample), exact acceleration of the current-node LP with
checked dual lifting, a genuine triangulation family realizing a
superconstant witness-screening gain, and controlled interfaces for composing
traces across larger regions.

The research article is the normative statement of assumptions and proofs.
`provenance/internal_review/` contains historical internal mathematical
review notes; the manuscript incorporates their final corrections.

`REPOSITORY_LICENSE.txt` preserves the pinned repository's license.
This report and the proposed additions were prepared with AI assistance
for the ProveIt research project. Full proofs and independent replay are
provided for external mathematical and code review.
