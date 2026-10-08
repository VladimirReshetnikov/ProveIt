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
The current full production suite passes 222 tests. Local report 10–12 production
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
