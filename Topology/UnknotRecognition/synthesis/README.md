# synthesis

The synthesized report on the six archives and on the new recognizer.

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
The current full production suite passes 344 tests. Local report 10–12 production
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
`data/minimal-window-integrated-tests.txt` records 344 passing tests; independent
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
