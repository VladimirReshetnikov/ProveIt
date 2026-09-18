# synthesis

The synthesized report on the six archives and on the new recognizer.

* `report.tex`, `acceleration.tex`, `report.pdf`: the report. Sections: sources and
  outcome; the six archives; code review; cross-validation; what is missing
  for `n^O(log n)`; the `fastunknot` recognizer; assessment.
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

## Experiment status (last observed 18 September 2026)

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
