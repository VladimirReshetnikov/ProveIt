# Intake 173: recovery and fresh runs

## Recovering the packages

`ZFC238_Research_2026-10-19.zip` arrived in `1cba633ec3`; the other five arrived in
`ec480205a1`. All were retired in placement `197ce3dc67`:

```bash
git show ec480205a1:"docs/incoming/ZFC_237_State_Construction_2026-10-19.zip" > ZFC_237_State_Construction_2026-10-19.zip
```

[`data/intake173-placement.json`](data/intake173-placement.json) lists every member
with its blob hash and role, as in batch 172. It was produced by the batch-172
placement script [`code/intake172-place.py`](code/intake172-place.py), with the
source list, batch number and pin field changed.

## Fresh runs of the intake

Python 3.14 and g++ 16.1 (WinLibs) on Windows, on fresh copies; no delivered file was
modified. The record is [`data/intake173-fresh-replay.json`](data/intake173-fresh-replay.json).

| Job | Result |
| --- | --- |
| Canonical census of every delivered table with 236–239 states | the five 238 packages: one table, `909f29c4…` (= `candidate-combined238`); the only 237: `7eda1da1…` |
| Source 106's fold as a row diff, re-applied to the 238 table | reproduces the delivered 237 table byte for byte (inherited labels) |
| Startup of the 237 table (`candidate-combined238/code/boot.py`) | exact frame after 409,835 steps; the fold's new rows unused |
| Unbounded runtime of the 237 table (Source 103's checker, unchanged) | `UNIVERSAL_MATHEMATICAL_PASS`: 8,386 cases, 2,261,369 rules (as delivered), all 474 rows, minimum duration 13 |
| Source 106 discovery, control on the 238 table | reproduces the receipt exactly: profile 33,545 runs, 18,811,196 steps, 27,995 pairs; 624 neutral helpers; 28,203 pairs, 669,196,927 helper checks, **one** candidate (235 → 98) |
| The same discovery on the **237** table | **0 candidates** (27,966 pairs, 651,775,278 helper checks) |
| The same discovery on 238 variants with delayed-erasure target 12 / 142 | only the 235 → 98 candidate in each |
| The same discovery on the corresponding 237 variants | **0 candidates** in each |
| Source 103's all-tape fold search (`--mode all --radius 9 --fuel 101`) on the 237 and 238 tables | 0 reductions on both, in all three modes (237: 12,059,883 abstract configurations; 238: 12,040,427); the search class does not contain the 235 → 98 fold |

The C++ programs had to be linked statically (`-static`). Built against the WinLibs
runtime but run from Git Bash, they otherwise load a mismatched `libstdc++-6.dll` and
crash at start. The source code is unchanged.

The variant tables are boundary239 plus the delayed erasure with row `80/0` going to
12 or 142, as in Source 101's `research/variants/`, with or without Source 106's
fold. Their startups take 409,943 and 409,967 steps, matching Source 101's figures.
They are search inputs only and are not published as candidates.

Not run: the packages' full replays, the TeX builds, the equational-packet generators
and rewrite searches, Source 104's displaced-head quotient search, Source 105's
source-depth search, and the inherited Lean and Rocq calibration.
