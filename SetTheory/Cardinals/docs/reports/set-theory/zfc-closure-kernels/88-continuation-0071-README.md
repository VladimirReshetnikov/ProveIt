# Source and compiler experiments

The principal retained artifact is `machines/normalized246_old.tm`, with its graph and physical roles beside it. It has **246 working states**, not fewer than 246. Its historical search label was `s9_best_007`.

The input and control files in this directory use the original physical labels, initial state 95, and halting label 254. The root `machines` directory also supplies canonical renumberings. Source-pair counts and binary working-state counts are different quantities.

## What is retained

| Historical label | Source pairs | Working states | Maximum source depth | Long-tail CD leaves | Universal frame audit | Blank bootstrap |
|---|---:|---:|---:|---:|---|---|
| `commute_106` | 203 | 246 | 34 | 18 | Pass at minimum gap 64 | Exact reference frame at 410,735 moves |
| `s3_best_010` | 202 | 246 | 39 | 12 | Pass at minimum gap 64 | Exact reference frame at 410,735 moves |
| `s7_best_018` | 203 | 246 | 43 | 10 | Pass at minimum gap 64 | Exact reference frame at 410,735 moves |
| `s8_best_005` | 202 | 246 | 39 | 11 | Pass at minimum gap 64 | Exact reference frame at 410,735 moves |
| `s9_best_007` | 203 | 246 | 40 | 8 | Pass at minimum gap 64 | Exact reference frame at 410,735 moves |
| `s10_best_004` | 203 | 246 | 45 | 10 | Pass at minimum gap 64 | **Uncalibrated** |

For the attempted eight-zero scanner, each long-tail decrement contributes two guarded cases. A long-tail increment can contribute one additional case. The selected normalized control has sixteen failing guarded cases after that scanner deletion; the original nine-zero scanner remains in the retained machine.

`s10_best_004` belongs only to `controls/`. Its source certificate allows operational control labels: 115 `CC2` occurrences become `CC3`, with every resolved successor preserved. All increment/decrement operands remain identical. Its binary instruction contracts pass, but its blank start has no inherited consistency calibration. The original start 95 was searched for 30,000,000 moves for an empty-root canonical frame with gap at least 64, nonempty natural spares, and logical `T = H = W = 0`; none was found. This bounded failure is not a proof of divergence or of eventual failure to initialize.

The search records for seeds 5 and 6 are historical source-search records, not accepted binary machines. The best source from seed 5 failed one universal control frame; seed 6 began from that unaccepted source. Their scores must not be interpreted as validated controls. Only the artifacts explicitly listed above have the stated audits.

## Deterministic selected-result replay

Run from the archive root:

```sh
python -B code/logic/replay_selected.py
```

This recomputes the physical entry mapping and borrowed-row filter of the `s7_best_018` input, imports the selected graph and roles, checks all 8,391 source cases, and re-emits exactly the 492 literal rows of `machines/normalized246_old.tm`. The output is `experiments/logic/selected_emission_replay.json`. This fixed-workload replay was run successfully after relocating the code into this archive.

The independent source and blank-prefix checks are under `code/audit`; the complete affine runtime driver is `code/check_runtime.py`. Their packaged root driver and the audit README give the corresponding commands. The emission replay is not a replacement for those proof layers.

## Rerunning the search

The Python scripts require only the standard library. They locate the included literal baseline at `vendor/context246` relative to their own path. They do not require the original scratch directory, a Git checkout, network access, or a proof-assistant installation.

Search outputs default to `experiments/logic/rerun`. Set the task-specific environment variable `ZFC_LOGIC_OUTPUT` to select another directory. The original searches had wall-clock budgets, so a repeated seed can reach a different number of proposals before its deadline on another computer. Historical proposal counts are recorded in `search_runs.json` and `runs/s*_summary.json`; they are finite observations, not exhaustive mathematical lower bounds.

The main normalization run was:

```sh
ZFC_LOGIC_OUTPUT=experiments/logic/rerun-normalize \
python -B code/logic/colored_generic_search.py \
  --seconds 300 --seed 9 \
  --rebase-graph experiments/logic/inputs/s7_best_018.json \
  --rebase-table experiments/logic/inputs/s7_best_018.tm \
  --suffix 2 --metric states
```

It examined 118,271 rotation recipes, admitted 28,262 distinct color candidates to the structural stage, and checked 7,996 exact source candidates. The best retained result was `s9_best_007`. A further 300-second run, seed 11, from that result examined 119,178 recipes without improving its score.

The preceding commuted-source search was:

```sh
ZFC_LOGIC_OUTPUT=experiments/logic/rerun-commuted \
python -B code/logic/colored_commute_search.py \
  --seconds 240 --seed 7 \
  --rebase-graph experiments/logic/inputs/commute_106.json \
  --rebase-table experiments/logic/inputs/commute_106.tm \
  --suffix 2 --metric states
```

The control-operand retargeting experiment was:

```sh
ZFC_LOGIC_OUTPUT=experiments/logic/rerun-retarget \
python -B code/logic/colored_retarget_search.py \
  --seconds 300 --seed 10 \
  --rebase-graph experiments/logic/inputs/s7_best_018.json \
  --rebase-table experiments/logic/inputs/s7_best_018.tm \
  --suffix 2 --metric states
```

That run examined 67,070 recipes and accepted 5,820 source-and-emission candidates; 4,217 of those had control operands differing from the rebased reference. Each emitted table still needs its independent runtime and bootstrap audits. The retained control `s10_best_004` is an intermediate positive source/runtime result, not the final heuristic-score optimum.

The additional search that preserves every row of the known bootstrap was:

```sh
ZFC_LOGIC_OUTPUT=experiments/logic/rerun-retarget-boot \
python -B code/logic/colored_retarget_boot_search.py \
  --seconds 300 --seed 12 \
  --rebase-graph experiments/logic/inputs/s9_best_007.json \
  --rebase-table experiments/logic/inputs/s9_best_007.tm \
  --suffix 2 --metric states
```

It examined 79,969 recipes and accepted 5,234 exact source candidates. None changed a control operand or improved the best physical-state count. Its filter froze the 264 rows of the certified blank trace; the union with the ordinary borrowed-row filter contained 286 rows.

The deeper finite start-95 survey of the uncalibrated control can be repeated with:

```sh
python -B code/logic/search_general_boot.py \
  --table experiments/logic/controls/s10_best_004.tm \
  --moves 30000000 \
  --output experiments/logic/controls/s10_dirty_boot_replay.json
```

The frame parser checks the entire finite support, left blank exterior, empty consumed address, header distance, each natural unary register block, and a nonempty spare suffix. Other initial states were surveyed separately in the state experiments.

## Search filters and proof obligations

The color search preserves selected borrowed rows, shared decoder entry contexts, and specified terminal suffixes. These are proposal filters based partly on finite execution data. They do not prove that every admitted table is correct. The final universal affine instruction checks quantify over all natural primary values, all extra nonnegative gap lengths, and all finite nonempty spare suffixes. The independently reconstructed source graph and full blank tape are checked separately.

The normalization emitter proposes existing direct entries for CI logical registers 1, 3, 4, 5, 6, 7 and CD logical registers 1, 3, 4, 5, 6. It adds no selector state. Other terminals retain their context constraints. The retargeting emitter additionally chooses an existing control row from observed `(kind, operand, four-bit suffix)` combinations, then validates the complete emitted table. An observed suffix combination is not itself a proof rule.

## Provenance

`rotation_search.py`, `grammar_stats.py`, `audit_phase.py`, `erase_known_zero_loops.py`, and `compile_rotated.py` are the small inherited parsing/rotation dependencies from the supplied second research archive, with paths adapted for this package. Their source program is the included Mira-Cult/Jeff Ketchersid literal `Prog254.v` snapshot. The color merger, generalized rebasing, commutation generation, selector normalization, operand retargeting, stronger-gap use, and selected emission replay are the present investigation's extensions.

The input `rebracket202_minimal.json` and `zfc_rotated246_old.tm` come from the supplied sixth research archive. The first decoder map and original borrowed-row record come from the second archive. The top-level provenance manifest records the pinned upstream repositories. Original authorship and inherited verification claims are not reassigned to this contribution.
