# synthesis

The synthesized report on the six archives and on the new recognizer.

`compressed_matching.tex` documents the exact arithmetic-progression occurrence
table, iterative local-window query, checked progression unions and polynomial
bit-complexity argument. The new whole-donor fallback preserves normal closure
without expanding oversized relators, and existing independent verifiers check
its moves. It is complete for occurrences of a specified pattern; searching
all partial cyclic overlaps remains separate work.

All 666 tests pass with optional Regina in 140.313 seconds. The controlled audit
retains 225 full knot queries, 30 capped Gordian group probes, 60 abstract
presentation runs and 135 exact substring queries. Existing knot paths are
unchanged. A supplied `a^N, b a^N b^-1 a` presentation that previously stalled
now finishes in two moves through `N=2^500`, about 7.7 ms including construction.
The exact table fallback can still take seconds on exponential negative queries;
no general subexponential recognition bound is claimed. Raw results are in
`../fast/results/compressed_match_20261008.json`, with test/build/benchmark logs
in `data/compressed-match-*`. The rebuilt article has 181 pages with no new
layout warnings or unresolved references.

`whitehead_powers.tex` proves an exact weighted-median formula for cyclic length
along powers of a selected Whitehead automorphism. The compressed producer
uses it on repeated directions or strongly compressed states. Version-3
certificates receive independent compressed or elementary replay. A compact
abstract presentation family that previously required exponentially many unit
moves now finishes in three moves, including the case with exponent `2^500`.
This is a local improvement, not a general subexponential knot-recognition bound.

The audit contains 225 full knot queries, 30 matched-cap Gordian group probes,
and 75 synthetic presentation runs, with shuffled historical A/A controls.
There is no material Gordian timing change and no power greater than one on the
knot corpus. A noisy small-case slowdown did not reproduce in 126 additional
queries retained separately. All 658 tests pass with Regina in 130.885 seconds;
the targeted follow-up also checks the repetition trigger after historical
allocations suppress the size trigger. Results are in
`../fast/results/whitehead_power*_20261008.json`, with logs in
`data/whitehead-power-*`. The rebuilt article has 176 pages, with no new layout
warnings. Regenerate the measurement tables with `make_tables.py`.

`adaptive_group.tex` adds one-way continuation from explicit to compressed
group search before a predicted substitution exceeds the letter allowance.
It preserves generator names, relator slots, completed moves and remaining
resources. No-switch traces retain explicit replay; switched traces undergo
independent compressed replay from the original PD. The article proves a
polynomial bound on the explicit prelude when the threshold is polynomially
bounded, while retaining the compressed search's completeness and complexity
gaps.

The 375-query audit preserves all fifteen default traces and records timings
near the explicit controls. Switching earlier at 4096 letters is slower on
Gordian, so the default threshold stays at the hard cap. In a separate
80-probe matched-cap audit, adaptive and always-compressed search verify all
forty of their probes while both explicit arms exhaust all forty. Caps affect
overlap availability and can substantially change the move sequence; these are
capacity results, not ratios against completed explicit recognition times.
Raw measurements are in `../fast/results/adaptive_group_20261008.json`.
All 653 tests pass with optional Regina installed in 126.251 seconds; see
`data/adaptive-group-integrated-tests.txt`. The rebuilt article has 171 pages,
with build output in `data/adaptive-group-article-build.txt`.

The latest prefix revision in `compressed_words.tex` adds bounded direct
cancellation walks and bisection beyond the prefix already proved equal.
In 375 measured queries, Gordian improves from 2.461 to 1.922 seconds including
replay; fourteen smaller cases total 185.27 versus 245.18 ms in summed medians.
All queries complete. Explicit search still wins at 1.259 seconds and 51.50 ms,
so it remains the default. The article proves the interval invariant and
records kernel regressions as well as gains. Raw samples are in
`../fast/results/compressed_prefix_20261008.json`; the benchmark separately
measures the direct walk and suffix-only bisection. No general sub-exponential
recognition theorem follows.
All 648 tests pass with optional Regina installed in 124.837 seconds; see
`data/compressed-prefix-integrated-tests.txt`. The rebuilt article has 168
pages, with build output in `data/compressed-prefix-article-build.txt`.

The preceding revision of `compressed_words.tex` explains indexed equality
assertions and a 64-step adaptive DAG probe with exact polynomial fallback.
The 375-query comparison loads the prior kernel from its recorded Git commit:
Gordian improves from 6.764 to 2.403 seconds, including replay, and fourteen
small cases total 248.40 versus 265.32 ms in summed medians. Explicit search is
still faster at 1.241 seconds and 51.46 ms respectively, so it remains the
default. Small periodic kernels show probe overhead; no uniform speedup or
general sub-exponential recognition bound is claimed. Raw samples are in
`../fast/results/indexed_equality_20261008.json`.
All 645 tests pass with optional Regina installed in 123.169 seconds; see
`data/indexed-equality-integrated-tests.txt`. The rebuilt article has 166 pages,
with build output in `data/indexed-equality-article-build.txt`.

The article also reviews Tomohiro I's deterministic recompression LCE index
as a further route for cancellation queries, recording its word-RAM assumptions
and the unresolved cost of changing the indexed text during our search.
That stronger query algorithm is not claimed as implemented.

The initial extension in `compressed_words.tex` adds optional compressed group
discovery. A shared DAG pass computes exact generator counts and weighted
Whitehead edges; presence/repetition masks identify unique generators.
Elimination and Whitehead transformations stay compressed, while relator
overlap discovery uses a bounded explicit bridge. All fifteen real knot
certificates pass both replayers, and random grammar tests check the summaries
against literal calculations.

The 225-query A/A/B audit records a regression: Gordian takes 7.076 seconds
with compressed search versus 1.247 seconds explicit, while fourteen small
cases total 391.33 versus 73.52 ms in summed medians. Defaults remain explicit.
Synthetic summaries and elimination handle lengths above 2^1024 with 3,077
nodes; that is a capacity result on supplied presentations, not a hard-knot
recognition bound. See `data/compressed-search-benchmark.txt` and
`../fast/results/compressed_search_20261008.json`. The detailed article states
the remaining search-length and grammar-growth obligations explicitly.
All 642 tests pass with optional Regina installed in 166.446 seconds
(`data/compressed-search-integrated-tests.txt`). The rebuilt article has 163
pages; its build log is `data/compressed-search-article-build.txt`.

`compressed_words.tex` describes the deterministic SLP word kernel and its
optional integration into independent group-certificate replay. Equality uses
split assertions and periodicity compaction; longest-prefix queries provide
exact free reduction and cyclic reduction. An audit compares noncanonical
words longer than 2^100 letters without expansion. A deliberately inflated
three-crossing unknot trace verifies with 904 grammar nodes and a 90-bit
intermediate word length, beyond the explicit checker's letter allowance.

Whole-query measurements show overhead on the current knot corpus: fourteen
small cases total 137.53 ms in summed medians versus 51.02 ms explicit, and
Gordian costs 1.417 versus 1.236 seconds. The extension remains opt-in; search
defaults to explicit and no general sub-exponential recognition theorem follows.
All 637 tests pass with Regina installed in 121.284 seconds
(`data/compressed-words-integrated-tests.txt`). Timing scopes, synthetic traces
and kernel counts are preserved in the raw benchmark artifact. The rebuilt
article has 161 pages.

`relator_overlap.tex` extends the native group certificate with a verified
normal-closure-preserving relator substitution, found by suffix automata.
The Gordian fixture now has a native certificate with 140 generator
eliminations and one overlap move. The search adapts to surviving rank:
Whitehead moves first through rank six, overlaps first above six, then the
other search when needed. All twelve original survivor traces are preserved,
and both formerly stalled mirror diagrams acquire group certificates.

Two 580-query experiments record the initial overlap-first regression and
the revised policy. In the adaptive run, Gordian completes 5/5 times at a
median 1.212 seconds including independent replay, versus Regina's 1.708
seconds; both older controls exhaust their four-second cap 5/5 times.
On 24 survivor/mirror inputs, the sum of medians is 84.86 ms versus 84.17 ms
for the prior group stage. The feature remains opt-in and establishes no
general sub-exponential bound. The article also records why a new generic
group-isomorphism preprint does not supply the missing knot-specific bound.
All 631 maintained tests pass in 122.185 seconds with Regina installed; see
`data/relator-adaptive-integrated-tests.txt`. The rebuilt article has 157 pages.

`group_certificates.tex` adds a bounded, independently replayed positive
recognizer based on reducing the complete Wirtinger presentation to one free
generator. It derives the Whitehead minimum-cut search and its conditional
expanded-word bound, and records a concrete convention mismatch in equations
(10)--(12) of Kapovich's arXiv:2607.21499v1 without treating that mismatch as a
refutation of the main results. The implementation retains the complete
fallback when group search stalls or exhausts its local allowance.

The 21-input A/A/B audit contains 441 timed queries. Group certificates decide
all twelve Khovanov-only survivors and improve ten of their median query
costs; the sum of medians drops from 60.8 to 39.2 ms including independent
verification. Regressions on some survivors and cheap RIII examples keep this
stage opt-in. All 626 tests pass with Regina installed in 126.707 seconds
(`data/group-integrated-tests.txt`). The rebuilt article has 154 pages;
`data/group-article-build.txt` records its build. These results do not provide
a general sub-exponential recognition bound.

`normal_surface.tex` explains an optional isolated Regina solid-torus
recognition stage after the cheap filters on undecided diagrams of at least
32 crossings. Local exhaustion falls back and global exhaustion propagates;
every interrupted child is killed and reaped. Results explicitly identify
external-engine trust rather than claiming an independently checked geometric
certificate. In five measured runs the portfolio decided the 141-crossing
Gordian unknot every time (median 1.788 seconds); both default controls
exhausted their four-second allowance every time. Other benchmark inputs
retain the existing fast paths. All 619 tests pass with Regina installed in
114.547 seconds (`data/normal-surface-integrated-tests.txt`); the focused
dependency-free run passes with three explicit optional-test skips. The
rebuilt article has 149 pages.

`treewidth_two.tex` adds a complete polynomial recognition procedure on
certified K4-minor-free projections. The structural classification reduces
this input class to connected sums of two-strand torus knots, so exact
determinant one is sufficient after the graph certificate passes. The
independent verifier uses a separate graph replay and Fox-matrix arithmetic.
The optional pipeline stage has a local deadline and safe fallback; its
capped form does not confer the standalone polynomial bound on Khovanov.
Fourteen paired whole-query benchmarks show 1.085–1.142x gains on three
mixed-sign two-strand unknot cases and regressions on several already cheap
Seifert cases. The stage remains optional. All 611 integrated tests pass in
126.455 seconds (`data/treewidth-two-integrated-tests.txt`). That checkpoint's
article had 147 pages.

`jones_detection_audit.tex` checks the combined residual-degree and geometric
realization claims in Carmi–Cohen arXiv:2606.22410v1. An explicit nine-crossing
anti-parallel replacement in a trefoil has Jones–Vassiliev degree 23, exceeding
the implied cap 22. Independent cube polynomials, formal coordinate conversion,
the twist skein recurrence, 79 smoothing traces and 1576 local RI deletions
support the finding. The audit does not disprove Jones unknot detection or
locate the faulty clasp-machine step; the proposed detection proof is not
adopted by the implementation.

The faithful decoder now skips normalization and coefficient decoding when
exact identity already proves the full polynomial is one. A preserved-source
paired benchmark reports 1.74x and 1.96x improvements on two tree medials,
with little change on other inputs. Full results agree in all arms, and all
603 integrated tests pass in 110.500 seconds; see
`data/jones-identity-shortcut-integrated-tests.txt`. Recognition does not request
full coefficient recovery, so these gains apply to full-Jones queries.
That checkpoint's article had 144 pages.

`faithful_jones.tex` proves that an input-sized exact quadratic evaluation
decides Jones polynomial identity without specialization collisions, and
recovers the full Laurent polynomial by balanced integer decoding. Counting
canonical color partitions gives an uncapped general bound of
`poly(n) * 2^O(sqrt(n)*log(n+1))` bit operations, even though the number of
colors grows exponentially. The adaptive tail needs a separate
quasi-polynomial estimate in this setting. Jones identity remains inconclusive
for recognition. Seven new tests include 156 independent cube-polynomial
comparisons, 187 bounded-polynomial recovery cases, real restarts and caps,
and very large JSON-safe witnesses. The invariant benchmark records the
cost of stronger guarantees without claiming a full recognition speedup.
The initial integration passed 602 tests in 111.769 seconds; that run is
recorded in `data/faithful-jones-integrated-tests.txt`.

`adaptive_potts.tex` defers separator construction according to actual query
work, proves a polynomial bound for a logarithmic remaining tail, and retains
the general subexponential fixed-color scalar bound. It explains why unchanged
orders continue the same table and why a restart spends only the original
remaining budget. The 595-test suite includes 120 independent cube-Jones
comparisons and actual policy/resource transitions. Seven-round measurements
separate 15 scalar scopes from 11 complete-recognition scopes, retain the
initial policy's regression and frozen source, and report remaining overhead.
The backend remains optional; the full recognition bound remains unresolved.
The literature note reviews Lackenby's compressed curve-operation theorems
without inferring an accelerated hierarchy bound from them.

`separator_orders.tex` proves the maintained optional separator order has
`O(sqrt(n))` crossing frontier for every closed classical projection. It explains
the BFS layers, contracted middle band, three paths at a dual-tree centroid,
independent hierarchy verifier, and comparison with the greedy order. Combined
with fixed-color exact Potts evaluation this gives a general subexponential
scalar query, **not** a general subexponential recognition algorithm. The
section states the remaining multiplicity and common-disk limitations, resource
semantics, 589 passing tests, and independent audit of 114 inputs. Measurements
separate preparation cost from scalar kernel work and retain capped outcomes.
The opening review also reassesses Lackenby's claim against the July 2026
preprint and distinguishes the earlier slides from later cubic-logarithm talk
abstracts. The claim remains plausible but its full complexity proof is not
established by the available specification.

`shadow_fallback.tex` extends the adaptive scheduler: exhausting marked work
retains direct Euler observations within the original shared query cap; query
exhaustion then continues the same exact scanner. It states the changed
zero-work semantics, separate fallback counters, cache/deadline invariants,
and the limited `O(nK)` bound on new closure geometry. All 582 tests pass
(`data/shadow-fallback-integrated-tests.txt`), including 200 scans checked
against independent homology across several budget combinations.
`../fast/benchmark_shadow_fallback.py` separates raw scans from recognition
and preserves both heuristic and explicitly supplied order results.

`tait_blocks.tex` follows actual marked-observer traces to optimize single
completion queries. The maintained shadow backend factors signed Tait graphs
at articulation vertices before dense allocation, keeping direct cofactors
through size 16. It proves the product formula with signed cancellation and
the retained global Jones phase, and explains deadline/budget behavior.
All 577 integrated tests pass (`data/tait-block-integrated-tests.txt`).
`../fast/benchmark_tait_blocks.py` measures initial queries, complete raw scans,
and complete recognition separately, with seven shuffled rounds and identical
controls. The initial cutoff-eight results are retained alongside the final
cutoff-sixteen results, so the scheduling choice and regressions are visible.
On the 352-crossing Conway sum the initial query improves 17.4x and the raw
scan 21.5x: the new observer stays within its local budget and reaches a later
Euler certificate. Full recognition still decides all measured inputs through
earlier filters, so no overall recognizer gain is established.

`boundary_reuse.tex` proves the new adaptive Euler path summaries and the
research cut-face Tait quotient construction. The maintained Euler evaluator
switches after four distinct same-stage queries when the suffix is sufficiently
long. All 572 tests pass (`data/boundary-connectivity-integrated-tests.txt`).
`../fast/determinant_research/audit_boundary_tait.py` verifies 4,503 actual
completions and 3,468 arbitrary boundary pairings, including classical pairings
that must decline this inherited-color representation.
`../fast/benchmark_boundary.py` records seven paired rounds with fresh setup:
adaptive Euler queries improve up to 15.8x on isolated long-suffix streams;
the research determinant path reaches 53.9x. The latter benchmark has no
interior elimination, and complete recognition shows no overall improvement.
Inputs, source hashes, timings, and audit counts are retained in
`../fast/results/boundary_reuse_20261008.json` and
`data/boundary-tait-audit.json`. Terminal kernels remain outside production.

`closure_resets.tex` reviews report 28's first-jet formula and pure-block
classical closure bounds, with the maintained optional `closure` backend.
It explains the total-rank invariant of a geometric reset, whole-summand and
knot-completion premises, bounded observation with exact fallback, and the
conditional complexity bound in the actual maximum reset gap. All 567 tests
pass (`data/closure-reset-integrated-tests.txt`).
The 29 delivered tests and the 160-diagram independent audit also pass against
current production. `../fast/closure_research/audit_upstream.py` reproduces
the latter without modifying delivered files. The source audit corrects one
geometry pin's association with the stated inspected revision and identifies
the retained fixture's omitted composition fast paths.
`../fast/closure_research/audit_blocks.py` records 624 completed scans of 312
knots, with no nonsingleton first-jet block found.
`../fast/benchmark_closure.py` measures full recognition and raw scans separately;
its samples are in `../fast/results/closure_reset_20261008.json`.

`determinant_continuations.tex` reviews report 26 and the optional maintained
`shadow` backend. It proves the marked-completion lower bound, derives the
signed Tait phase and residue reconstruction, and explains budget exhaustion
with exact continuation of the same scan. It also reviews the singular-safe
terminal kernel and the new checked common-graph producer. The latter accepts
3,186 connected queries; another 1,317 have disconnected projections and zero
determinant specialization. This finite audit is not a universal complexity
bound, and terminal reuse is not enabled in the recognizer.
`data/determinant-integrated-tests.txt` records all 560 passing tests.
The archive validation and actual-upstream reruns are retained in
`data/determinant-archive-validation.txt` and
`data/determinant-upstream-probe.json`; the geometric audit has inputs and
source hashes in `data/determinant-terminal-geometry-audit.json`.
`../fast/benchmark_shadow.py` reproduces separate paired recognition and raw
scan timings in `../fast/results/marked_shadow_20261008.json`.

`causal_r3.tex` reviews report 27's parameterized search, reproduces its
5,000-system and 608,400-instance abstract audits, and gives a four-site
counterexample to immediate-inverse pruning when accumulated support controls
the birth budget. The production changes fix RIII trace ambiguity by recording
input face darts and add opt-in clustered/adaptive search with guarded inverse
pruning, exception-safe rollback and global deadline checks. The default
search also stops deepening when no legal first RIII move exists.
`data/causal_inverse_audit.py` reproduces the counterexample.
`data/reidemeister-trace-integrated-tests.txt` records 539 passing integrated tests.
The later search integration passes 550 tests, recorded in
`data/causal-r3-integrated-tests.txt`.
`../fast/benchmark_causal_r3.py` reproduces the paired end-to-end and isolated
timings; `--discovery` reproduces the random search, the negative findings,
and exact trace comparisons against the pinned default implementation.
The opening source review also distinguishes Lackenby's announced
`2^O((log n)^3)` bound from this project's stronger `n^O(log n)` target and
explains why the hierarchy strategy is plausible without claiming a verified
general runtime bound.

* `report.tex`, `acceleration.tex`, `round3.tex`, `bend.tex`, `report.pdf`: the report (updated with the October continuations). Sections: sources and outcome; the six archives; code review;
  cross-validation; what is missing for `n^O(log n)`; the `fastunknot`
  recognizer; assessment; the nine acceleration proposals, 0.2 and the Rust
  port (`acceleration.tex`); the later constant-factor work on the Python
  package, its negative results, and how it was measured (`round3.tex`); the port to
  Bend 2 and what its parallelism delivered (`bend.tex`; the port itself,
  directory `bend/` of the standalone Knots repository, was not carried into
  ProveIt).
* `build.sh`: regenerates the tables and runs `pdflatex` twice.
* `make_tables.py`: writes `tables/*.tex` from the JSON files in `data/` and
  from `../fast/results/benchmark.json`.
* `data/`: the cross-validation scripts and their outputs.
  * `khovanov_xval.py` / `.json`: five Khovanov implementations (archives 02–06)
    on 44 shared inputs; all agree.
  * `pattern_xval.py` / `.json`: six ball-pattern testers on 2000 random
    spherical cubic rotation systems and six named patterns; all agree.
  * `grid_xval.py` / `.json` / `grid_xval_output.txt`: archive 01's grid search
    against archive 04's Khovanov rank on every grid of size ≤ 6 and random
    grids of size 7–9; no disagreement.
  * `scan_stress.py` / `scan_stress_output.txt`, `profile4.py` /
    `profile4_output.txt`, `scan_smoke.py`: the scanning Khovanov computation
    of `../fast` against archive 04's cube on 120 random braid closures, and
    step-by-step profiles.
  * `lackenby2026-extracted-text.txt`: text of arXiv:2607.23350v1 as extracted
    for the review; the preprint's source is in `../docs/arXiv-2607.23350v1/`
    (Section 9, "The number of steps", is the relevant part).

## October 2026 continuation

`structural.tex` maintains the theory and integration review of research report 07.
The Python implementation now includes its certificates and shared scanners;
the delivered research archive is unchanged. Local validation: 69 integrated
tests passed on CPython 3.13.14. Reproduce paired recognition measurements and
exact scanner checks with `../fast/benchmark_structural.py`; local data are in
`../fast/results/structural_integration_20261007.json`. These measurements are
separate from the authors' archive data and from end-to-end CLI timings.
The post-reduction certificate extension is also described there; all 71 tests
pass. Its isolated comparison is `../fast/benchmark_reduction.py`, with paired
samples in `../fast/results/reduction_structural_20261007.json`.
The next extension prepares suffix-Euler geometry lazily within the inference
budget; that checkpoint had 73 passing tests. Setup-only measurements and
separate allocation peaks are in `../fast/results/lazy_euler_setup_20261007.json`,
reproduced by `../fast/benchmark_euler_setup.py`.

`research_updates.tex` covers the later report 08–12 intake and reviewed
integrations: complete short-strand braid recognition, interlacement factors,
sparse Alexander elimination, and the corrected general-frontier matching bound.
That production checkpoint passed 431 tests. Local report 10–12 production
cross-checks are retained in `data/`. Report 12's exact component contraction
is integrated as an opt-in API/CLI option. Report 11's twist backend is now
integrated too; report 12's structured block cancellation remains under review. The braid benchmark includes PD construction and keeps the current
Seifert shortcut enabled in its baseline. Reproduce it with
`../fast/benchmark_braid.py`; raw data are in
`../fast/results/braid_integration_20261007.json`.

`radical.tex` reviews the incoming radical-transfer archive and proves the
production survivor-profile and degree-gap shortcut. Its adaptive variant
preserves completed sparse pivots and switches implementations after a Schur
update allowance. A failed shortcut resumes the same complex. It remains an
opt-in strategy: ordinary scans show little change, while dense synthetic
two-term complexes improve substantially. The full 222-test log is
`data/radical-integrated-tests.txt`; archive reruns and validation summaries
are the other `data/radical-*` files. Reproduce paired standard/eager/adaptive
timings with `../fast/benchmark_residue.py`. The table generator reads its
recorded `../fast/results/residue_integration_20261007.json`.

`homogeneous.tex` reviews the next dense-algebra report, derives the recovered
quantum grading and improved component-type bound, and explains the integrated
homogeneous and top-degree coefficient shortcuts. The 229-test checkpoint is
`data/homogeneous-integrated-tests.txt`. `../fast/audit_grading.py` audits the
current scanner with ordinary and forced component algebra (520 scans).
`../fast/benchmark_homogeneous.py` compares the previous ranked and new dispatch,
and `../fast/benchmark_adaptive_graded.py` supplies graded synthetic controls for
the adaptive policy. Their results are retained in `../fast/results/`; the
table generator reads them directly. Mixed-degree adaptive controls remain
historical measurements of valid ungraded complexes and cannot be interpreted
as genuine graded scan differentials. The report's finite-quotient search has
been tested in isolation but is not integrated into the current recognizer.

## Historical experiment status (18 September 2026)

Read this before rerunning anything: two of the scripts take hours, and one
of them was deliberately stopped.

| Script | Status | Wall time | Notes |
|---|---|---|---|
| `khovanov_xval.py` | completed | ~1 min | 44 inputs, five packages, 0 disagreements; output `khovanov_xval.json` |
| `pattern_xval.py` | completed | ~2 s | 2000 random + 6 named patterns, six testers, 0 disagreements; output `pattern_xval.json` |
| `grid_xval.py` | **stopped after size 9** | ~2 h | sizes 2–6 exhaustive (3 s), size 7 (7 s), size 8 (39 s), size 9 (**6775 s**, one grid needed 900 863 search states). Size 10 was never run: the script was killed and `grid_xval.json` was assembled from the completed lines of `grid_xval_output.txt`. Rerunning as-is will attempt size 10 (60 grids) and may take a day; lower the sizes first. The cost is in archive 01's search, not in the Khovanov side, which is capped at 14 crossings. |
| `scan_stress.py` | first three sections completed; last section never ran | ~2 min for the completed part | 120 random braids vs. archive 04 (0 mismatches), Atlas knots, unknot family: all in `scan_stress_output.txt`. The final "random 4-braid" section as committed generates **even-length words on four strands, which can never close to a knot**, so its loop spins forever; the run was killed. Use odd lengths (as `profile4.py` does) before rerunning. |
| `profile4.py` | completed | ~1 s | odd-length 4-braid closures, step-by-step; output `profile4_output.txt` |
| `scan_smoke.py` | completed | seconds | first agreement check of the scanner with archive 04 |
| `../fast/benchmark.py` (version 0.1) | completed | ~11 min | recorded as `../fast/results/benchmark_0.1.json`; one input (random 36-letter 5-braid) hit the 600 s cap. Under 0.2 that input takes under a second |
| `proposals_bench.py` | completed | ~50 min for all engines | every engine (0.1 baseline, nine proposals, 0.2) on 20 tasks, fresh process each, 120 s cap. Long because the baseline and the proposals without min-fill pivots or without factorization run into the cap. Outputs: `proposals_bench_proposals.json` (the nine), `proposals_bench_base_new.json`, `proposals_bench_rank_rerun.json` (rank task through factored APIs). **Ignore the `base` rows inside `proposals_bench_proposals.json`**: during that run `base` pointed at the working tree, which was being edited; the valid baseline rows are in `proposals_bench_base_new.json`, measured against the byte-identical 0.1 copy in `../proposals/01/baseline` |
| `../fast/ablation.py` | completed | ~40 min | per-idea ablation of 0.2; the LIFO rows on the stress case hit the 300 s cap on purpose |
| `../rust/profile.py` | completed | see `../rust/README.md` | timings and phase split of the Rust binary |

Everything cited in `report.pdf` comes from completed runs; the two
interrupted ones contributed nothing beyond what is listed as completed.

The cross-validation scripts import the archives' packages side by side; they
were run from a scratch directory containing copies of `reports/0k/<package>`
renamed to `kh02`, `kh03`, `kh04`, `kh05`, `kh06` and `grid01`. To rerun
them, recreate those copies (the packages use only relative imports) and
adjust the `sys.path` lines at the top of each script.

The component-contraction theory and production integration are maintained in
`research_updates.tex`. Local exact algebra, degree, and CLI resource regressions
are in `data/component-algebra-tests.txt`; separate dense/sparse kernel and raw
scanner timings are in `../fast/results/component_algebra_20261007.json`.
The ordinary scanner cases did not select adaptive dense calls, so these
measurements do not support a default-engine switch.


`twist.tex` explains the checked twist backend, its exact basis and degree
profiles, its quasi-polynomial bound for logarithmically many supplied braid
runs, and the sharper linear scaling when one block grows in a fixed context.
The backend remains optional and does not supply short-run presentations for
arbitrary PD input. `data/twist-integrated-tests.txt` records the 209-test suite.
Raw homology measurements and controls are in
`../fast/results/twist_integration_20261007.json`; the extended four-strand
context experiment is in `../fast/results/twist_context_scaling_20261007.json`.

`windows.tex` proves report 13's exact moving homological interval, including
both guards, pre-allocation pruning, mirror selection, and the conditional
quasi-polynomial query bound. It explains the new optional adaptive widening
stage, local budgets and complete fallback, and compatibility with adaptive
cancellation. `../fast/benchmark_windows.py --output FILE` reproduces the
seven-round comparisons in `../fast/results/window_integration_20261008.json`.
The table generator reads that file. `data/window-integrated-tests.txt` records
245 passing tests; report 13's 64 scanner and 10 hierarchy tests and report
14's 94 tests have separate logs in `data/`. The subsequent interval and scalar
splitting integration is documented in `continuations.tex`.

`continuations.tex` integrates report 14's exact interval normalization,
length-two decision quotient, and certified scalar splitting. The production
splitter now restricts scalar changes to recovered quantum-shift blocks by
default. The section derives a sharper homogeneous checkpoint bound and
keeps its hypotheses explicit. `data/continuation-integrated-tests.txt` records
267 passing tests; `data/continuation-algebra-validation.json` records the
independent 861-complex, 10206-comparison finite algebra check. Reproduce paired
measurements with `../fast/benchmark_continuations.py --output FILE`; retained
results are `../fast/results/continuation_integration_20261008.json`. They
include actual split witnesses and negative timings; the table generator reads
them directly. The report's order optimizer is not integrated.

`ranktwo.tex` reviews and integrates the incoming rank-two braid-kernel archive:
exact local normal forms, optimal bounded-overlap interval search, independent
linear replay, and the conditional small-core recognition theorem. It also
proves why the supplied higher-rank barrier cannot be solved by repeated strict
rank-two shortening. The optional production stage has a local budget and
preserves evidence across a restart on the verified shorter source braid.
`data/ranktwo-integrated-tests.txt` records 272 passing tests; archive tests
and the formerly unrun real-upstream gateway check have separate logs.
`../fast/benchmark_ranktwo.py --output FILE` measures complete recognition with
all default filters and PD construction, retaining timings, transcripts, and
separate allocation peaks in `../fast/results/ranktwo_integration_20261008.json`.

`extremal.tex` reviews the incoming extremal-window report and explains the
new optional cancel-before-truncate strategy on the current production scanner.
Its nice-order certificate and minimal-truncation domination proof transfer the
primary paper's binomial object bounds to arbitrary exhaustive pivots. The
section distinguishes this from the faster allocation-pruned strategy, includes
the raw-depth padding obstruction, and accounts for bounded composition caches.
`data/minimal-window-integrated-tests.txt` records 277 passing tests at that checkpoint; independent
archive tests and the 393-window audit have separate logs. Reproduce paired
query measurements using `../fast/benchmark_minimal_windows.py --output FILE`;
raw results are `../fast/results/minimal_windows_20261008.json`.

`potts.tex` integrates report 17's exact quadratic Jones specializations,
equality-pattern transfer and processed-component factoring. It proves the
half-frontier and component-frontier bounds, explains the exact five-color
collision family, and documents resource-safe optional API/CLI dispatch.
The archive passed 172 tests and the production checkpoint passed 315.
`data/potts-independent.json` records 4,464 independent cube comparisons per
exact backend and 45 larger weaving checks. The paired benchmark in
`../fast/results/potts_20261008.json` separates equal-specialization kernels
from normal recognition and includes regressions; defaults remain unchanged.

`disk_transfer.tex` integrates report 21's geometric certificate and full finite
radical transfer as the opt-in `disk-adaptive` policy. The source-derived fixture
passed the pinned Git-blob AST audit; 52 archive and 344 production tests pass.
Independent geometric/cube checks and seven full typed chain-homotopy
certificates are retained in `data/disk-*`. The section includes the descending
grid raw-width obstruction and the current scheduler's resource/fallback scope.
Paired data in `../fast/results/disk_transfer_20261008.json` distinguish
synthetic gains from four ordinary scans with zero full-transfer calls.

`twist_continuation.tex` reviews report 18 and documents the exact one-run
recurrence, positive turnback slope, compact output, streamed storage and
source-braid structural specialization. It distinguishes exact homology gains
from the already-decidable dominant-run recognition family. At that integration checkpoint, all 254 archive
and 391 production tests passed; separate audits checked 832 recurrence
comparisons, 220 independent cubes and 500 slope identities. Data are in
`data/twist-*-audit.json`; paired measurements are in
`../fast/results/twist_tail_20261008.json`, `twist_streaming_20261008.json`,
and `braid_profile_20261008.json`. The streaming regressions and differing
input/output contracts are stated explicitly; defaults remain unchanged.


`rational.tex` reviews report 22 and documents the complete arithmetic
Montesinos classifier, checked-source integration and optional literal local
obstructions. It proves the bit bounds and separates the four-ended Boolean
continuation-rank and explicit-full-complex barriers from general running-time
claims. At this checkpoint the production suite had 411 passing tests; the unchanged archive
has 152. Independent results in `data/rational-*` cover 1,200 sources,
1,398,101 identity entries, 21 checkpoint diagrams and adversarial local maps.
Raw paired measurements are in `../fast/results/rational_20261008.json`.
Object-capped baselines are censored; local regressions and construction versus
recognition scope are retained explicitly. Reproduction commands are in
`../fast/rational_research/README.md`.


`graded_transfer.tex` integrates the quantum-ordered full transfer from report
23, with eager and adaptive policies. It proves termination and source-band
pruning without the disk-transfer geometry precondition, retains nonzero maps
between scalar survivors, and charges allocated slots left by sparse pivots.
The 426-test maintained suite and 281-test delivered snapshot pass; the latter
also contains additions not yet integrated. The production transfer audit
checks 1,812 stage contractions across 86 diagrams and 258 order presentations.
All 114 pinned source blobs match. Evidence is in `data/graded-*`; paired raw
scanner/kernel measurements are in `../fast/results/graded_transfer_20261008.json`.
The remaining report 23 proposals are reviewed below; report 24 scanner integration is described below; its surface-cover kernel remains under review.


`symbolic_runs.tex` completes the report 23 review: the existing run frontend
now supports exact hexadecimal integers and independent serialized-certificate
replay. It documents the earlier total-rank law without claiming a smaller
reference calculation, sharpens the succinct context bound, and states the
repair-DAG theorem with its unresolved geometric hypotheses. Evidence includes
392 explicit tail complexes, 380 weighted-path fixtures, and 431 maintained
tests in `data/tail-earlier-threshold-audit.json`, `repair-dag-audit.json`, and
`symbolic-integrated-tests.txt`. The production backend keeps one canonical
tail implementation; the DAG calculation remains a research diagnostic.


`corridor_transfer.tex` integrates report 24's exact survivor pruning and
bidirectional full transfer, including the sparse scalar and Boolean-port
variants. The article proves the propagation bounds and complete fixed-algebra
stage separation, charging scalar setup, graph construction, endpoint masks,
and vertex visits explicitly. It distinguishes the constructed complex from an
unproved knot-prefix family. The default reducer remains sparse cancellation.
All 458 maintained tests pass; production repeats 3,885 transfer comparisons
on 555 prefixes with full contraction certificates, 639 support comparisons,
and the sparse/packed scalar-map representation audit. Evidence is in
`data/corridor-*`; the 11-arm paired measurements are in
`../fast/results/corridor_integrated_20261008.json`. The delivered archive's
268 scanner tests and separate cover suite pass in a temporary copy. Its 20
integration hashes match; its advertised package-wide hash manifest is missing.
The separate cover-kernel follow-up is now maintained in `surface_covers.tex`,
with its supplied-presentation contract kept distinct from recognition.


`cyclic_garside.tex` reviews and integrates report 25's exact classical Garside
normal forms, shared cyclic interval optimizer, independent local replay and
bounded source-braid portfolio. It gives explicit word-operation and storage
bounds, a restricted inflated-core quasi-polynomial theorem, and two limitations
of equality-based shortening. Production puts modular Alexander
first, reuses that inconclusive check if the probe declines, and runs Jones after
the probe so that compression can avoid work on the larger diagram. That checkpoint
passes 517 tests, including 60 small-closure homology comparisons and resource,
restart and certificate regressions. Logs and the 45-hash/six-blob source audit
are in `data/cyclic-garside-*`. Reproduce the separate mechanism and complete
recognition experiments with `../fast/garside_research/benchmark_kernel.py` and
`benchmark_pipeline.py`, each with `--output FILE`. Their paired raw results in
`../fast/results/cyclic_garside_*_20261008.json` generate the article tables.
The `before_filter_order` and `after_all_filters` files retain the diagnostic
regressions that motivated placing the probe between modular Alexander and Jones.
They are explicitly not measurements of the final implementation.


`surface_covers.tex` completes the report 24 cover-kernel review and proves the
new ordered-point signature and rooted transport interface. It also shows why
two marks already allow `W` inequivalent types on a single cyclic annulus cover.
The geometry module remains separate from recognition: a checked extraction
from a knot exterior, full attachments and a search-state bound are still needed.
The 534-test checkpoint, 13,846 expanded-topology comparisons and independent
196,712 marked-equivalence comparisons are retained in `data/surface-cover-*`.
Use `../fast/cover_research/audit_markings.py --output FILE` and
`../fast/cover_research/benchmark.py --output FILE` to reproduce the new audit
and geometric measurements. The tables read `../fast/results/surface_cover_20261008.json`;
its 12 complete-topology cases and nine prepared-query cases have raw paired
samples, A/A controls and source hashes. They are not knot-recognition timings.
