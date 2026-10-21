# New 214-state reduction searches and a concrete selector obligation

**No 214-state construction was found.** These reproducible bounded searches supplement the proof-simplification report. Failed finite-window joins are not semantic counterexamples and do not establish a state-count lower bound.

All machine inputs and inherited discovery/checking scripts are pinned in `provenance.json`. All runs used exact native tables. The bundled standard-library Python scripts neither need network access nor modify the shipped machines.

## New physical screens

| Seed | Radius / fuel | Inductive contexts | Candidate quotient specifications | Hits |
|---|---:|---:|---:|---:|
| CM215 | 7 / 97 | 972,655 | 315,436 | 0 |
| K215-R41 | 7 / 97 | 980,047 | 316,292 | 0 |
| Final ST215 (append-zero) | 7 / 97 | 971,509 | 310,300 | 0 |

These final seeds were not the primary/append-one seeds in the inherited physical-search report. Each unordered state pair is merged; the inherited branch choices are tried, and if one branch agrees, every write/direction/remaining-target choice is tried for the other. The finite domain includes every initial 15-cell window at initial control 0, closes under both possibilities for newly entering exterior cells, and is explicitly checked inductive. A positive independent-checker result would establish an all-initial-tape simulation by bounded positive blocks. None passed the discovery filter here.

## A stronger prefix-conditioned helper search

The previous CM215 helper search assumed only the predecessor marker. `context_helper_search.py` retains the entire exact source prefix at each of the eight occurrences of roles 52 and 176. It tries all 856 replacement actions for CM215 row 52/0 after removing 176, requires the exact target 168 or 154 at head+1 and complete restoration of every visited cell, and branches on arbitrary exterior bits. Bounds: 500 transitions after the first row, 24 additional cells, 16,384 branch nodes per case. No replacement passed. The existing helper is a positive control on all eight contexts.

## Two-row synthesis

`two_row_marker_reentry.py` tries fusing helper 176 into every one of the other 214 states. Each row independently ranges over 860 actions (two writes, two moves, 215 remaining-or-halt targets). It allows reentry into the synthesized read branch but rejects paths that need the unknown other branch before joining. There are 368,080 individual row tests. Exactly one branch passed: keep 211/read 1 = `1 R129`; no complete pair passed. This is an incomplete synthesis family.

The more focused `two_row_cut_search.py` removes helper 176 as an internal control without requiring a state-map image for it. It simultaneously changes 52/0 and 211/0 and requires joins only at retained controls. Of 860 candidate 211/0 actions, the preliminary provider screen retained:

```
0 L52; 0 L165; 0 L193; 0 R159; 1 L52.
```

All 4,300 entry/provider pairs failed the radius 7/fuel 97 join screen. The preliminary screen permits entry to the as-yet-unknown 52/0 row; the completed pair is tested with both rows fixed.

## The precise remaining mathematical opportunity

The six incoming-edge facts checked by `check_near_miss.py` prove on **every tape started at control 0**:

1. At helper 176, if the current bit is 0, the predecessor bit is 1.
2. At role 211, the predecessor bit is 0.
3. Both read-one branches are `1 R129`.
4. The required read-zero branches are `0 R185` and `0 R159`, respectively.

For (1), 176 is entered only by 52/0, which moves left. If that predecessor bit is 0, 52 could only have been entered by 165/0 or 193/0. Every incoming edge to 165 and 193 writes 1 and moves right. Hence the bit one further left is 1. For (2), 211 has the unique incoming edge 220/0, which writes 0 and moves right. Initial control 0 is none of these intermediate controls.

Consequently a second conditional-origin fold is semantically justified: distinguish these roles by the predecessor bit only on current 0. The outstanding problem is implementing the selector cheaply. A literal three-step implementation needs unchanged providers with rows `0 R159` and `0 R185`; the only such providers are 211 (which must be rewritten) and 176 (which must be deleted). This blocks that particular provider template, not all possible implementations. A successful 214-state construction needs a more general continuation block, one additional safe row rewrite, or a changed source/interpreter invariant.

## Reproduction

From this directory, with Python 3 and assertions enabled:

```sh
python3 -B code/check_near_miss.py
python3 -B code/context_helper_search.py --inputs inputs --output /tmp/prefix-helper-result.json
python3 -B code/search_folds.py --table inputs/cm215.native.tm --radius 7 --output /tmp/cm215-fold-rerun
python3 -B code/search_folds.py --table inputs/r41.native.tm --radius 7 --output /tmp/r41-fold-rerun
python3 -B code/search_folds.py --table inputs/st215.native.tm --radius 7 --output /tmp/st215-fold-rerun
python3 -B code/two_row_marker_reentry.py --checker code/vendor/check_joint_fold.py --table inputs/cm215.native.tm --radius 7 --output /tmp/cm215-two-row-rerun
python3 -B code/two_row_cut_search.py --checker code/vendor/check_joint_fold.py --table inputs/cm215.native.tm --radius 7 --output /tmp/cm215-cut-rerun
```

Timing is not part of a receipt identity. No positive candidate or proof-assistant endpoint is included in this research supplement.
