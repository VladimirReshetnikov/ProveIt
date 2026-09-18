# synthesis

The synthesized report on the six archives and on the new recognizer.

* `report.tex`, `report.pdf`: the report (12 pages). Sections: sources and
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

The cross-validation scripts import the archives' packages side by side; they
were run from a scratch directory containing copies of `reports/0k/<package>`
renamed to `kh02`, `kh03`, `kh04`, `kh05`, `kh06` and `grid01`. To rerun
them, recreate those copies (the packages use only relative imports) and
adjust the `sys.path` lines at the top of each script.
