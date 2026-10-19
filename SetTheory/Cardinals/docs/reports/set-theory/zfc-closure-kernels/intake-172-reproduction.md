# Intake 172: recovery and fresh runs

## Recovering the packages

The three archives arrived in `83fd358548` and were retired in placement
`07194e5b4d`. Recover any of them with

```bash
git show 83fd358548:docs/incoming/BusyBeaver239_Research_2026-10-19.zip > BusyBeaver239_Research_2026-10-19.zip
```

and likewise for `ZFC239_Companion_2026-10-19.zip` and
`ZFC_239_State_Construction_2026-10-19.zip`. [`data/intake172-placement.json`](data/intake172-placement.json)
lists every member with its git blob hash and role: `root`, `code` or `data` with
its shipped path; `alias` with the existing path of the same blob; or `archive-only`.
Placed files are byte-identical to the delivery. Text files are subject to the
repository's line-ending normalization, which the intake rules ignore.

The placement script is [`code/intake172-place.py`](code/intake172-place.py)
(`python code/intake172-place.py EXTRACT_ROOT REPO` prints the plan; `--apply` copies
the files and writes the map, without `git add`). It decides aliases against the
files tracked at run time, so it reproduces this placement only when run on the
placement's parent `83fd358548`. Its rules are those of `docs/incoming/README.md`
section 3. Shipped names are
`NN-slug-<member path with / replaced by ->`. A delivered script that names its
neighbours by their delivery paths must therefore be run from a fresh extraction of
the archive, not from the shipped copies.

## Fresh runs of the intake

All runs used Python 3.14 on Windows, on fresh copies of the extracted packages. No
delivered file was modified. The record is [`data/intake172-fresh-replay.json`](data/intake172-fresh-replay.json).

| Job | Command (from the package root of a fresh copy) | Result |
| --- | --- | --- |
| Source 103 quick replay | `python -B reproduce.py` | PASS, 8/8 checks |
| Source 103 runtime, boundary239 | `python -B validation/check_literal_runtime.py --table candidate239/zfc_boundary239_old.tm --sites candidate239/sites_logical.json --states 239 --output …` | `UNIVERSAL_MATHEMATICAL_PASS`, 2,247,513 rules, as delivered |
| Combined 238 runtime | the same checker with `--table zfc_combined238_old.tm --states 238` | `UNIVERSAL_MATHEMATICAL_PASS`, 8,386 cases, 2,255,513 rules, 476 rows, minimum duration 13 |
| Negative control | the same checker on the 238 table with `91/1` restored to `0 L 50` | `NOT_PROVED` at the 49th case (site 35) |
| Startups | `candidate-combined238/code/boot.py` on rotation240, delayed239, boundary239 and combined238 | exact frames after 409,691, 409,835, 409,691 and 409,835 steps |
| Fold certificates | `candidate-combined238/code/fold_any.py` on rotation240 → delayed239 (control) and boundary239 → combined238 | PASS; the control reproduces Source 101's 121,536 windows |
| Guard | `candidate-combined238/code/guard_any.py` on boundary239 | PASS: 32 visits, constant ≥ 23, 6 blank-prefix visits |
| Guard control | `guard_any.py` on rotation240 with its own source | running when this note was written; its result is added by the catalogue commit |

The drivers `boot.py`, `fold_any.py` and `guard_any.py` were written for this intake.
They are parameterized re-implementations of Source 101's `check_boot239.py`,
`verify_guarded_fold239.py` and `certify_guard169.py`. The mathematics is unchanged;
the hash pins and the constants specific to the 240-state table are computed from the
inputs instead. `guard_any.py` imports Source 103's `validation/symbolic_runtime.py`
unchanged. Source 101's and Source 103's engines differ only in comments and in the
source hash that `validate_inputs` pins, a function `guard_any.py` does not call.

Not run: Source 101's and Source 102's own full replays, each package's C++
discovery searches, the TeX builds, and the inherited Lean and Rocq calibration. The
runtime checker's soundness rests on the audit in
[`data/101-coord239-evidence-UNIVERSAL239_AUDIT.md`](data/101-coord239-evidence-UNIVERSAL239_AUDIT.md)
and on the earlier intakes of the same engine (batches 169 and 170). This intake did
not re-audit it.
