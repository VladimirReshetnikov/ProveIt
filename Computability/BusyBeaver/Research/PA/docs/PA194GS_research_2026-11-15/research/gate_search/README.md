# Gate search, corrected model, and audit record

The delivered, fully checked construction is in `../../machine`. This directory records the search for a strict reduction and distinguishes a subsequently discovered price-model error from the corrected work. A search score is not a physical correctness proof or a state lower bound.

## Use the corrected model

The default replay is `corrected/`. It uses the literal copyH remainder entry **179**, performs graph reachability before charging fixed controls, and checks simultaneous two-cell folds among reachable controls. The nominal goal is an effective cost at most 60 relative to the original 133-control fixed budget. The reachability adjustment is included in that effective cost, so disappearing fixed controls are charged correctly.

From `corrected/`:

```sh
g++ -O3 -std=c++17 search.cpp -o search
./search H.seeds.txt leaf_attrs.txt replay_h 300 18112200 4000000
```

Use `GDH.seeds.txt` and random seed 18112201 for the GDH run. `search_warm.cpp` uses a warmer annealing schedule and more two/three-rotation proposals; its H/GDH runs use seeds 18112202 and 18112203, a 120-second limit, and at most 2,000,000 proposals. `results.json` and the four logs record the actual outcomes and proposal totals. Wall-clock limits prevent exact cross-processor reproduction of the number of proposals, but the input snapshots and random seeds are fixed.

Every `*.seeds.txt` contains the complete fixed transition table and initial DAGs. The scorer and annealer therefore run without the original repository. Neither source-CFG identity nor complete physical contracts are inferred merely from a favorable score. Any smaller nominee must still pass exact source control-flow checking, local folds, universal tape contracts, and complete blank startup.

## Corrected repricing of saved grammars

`corrected_repricing/` freezes the 900 saved grammars from the earlier searches as five template files, together with the appropriate fixed tables, template-to-origin metadata, all individual price outputs, and a standalone corrected scorer. All **900 price at 194** after the binding and reachability corrections. None is a surviving 193-state nominee. This is still a scoped cost-screen result, not full verification of 900 machines.

For one group, from `corrected_repricing/`:

```sh
g++ -O3 -std=c++17 screen.cpp -o screen
./screen cc422ef0d2.seeds.txt replay 600 1 compatible
```

The final arguments mean 600 templates, one parameter combination per template, and simultaneous compatibility checking. The metadata files give the template count and fixed budget for each other group. The generic screen's `hits` output uses an effective-cost threshold of 61, so it includes 194-state prices; consult `summary.json` or add the group's fixed count to its effective score.

## Why the historical scores are qualified

The inherited expanded-copy search represented the source macro `node69` by native entry 30 and recognized `(19,30)` as a free copyH reader. The literal machine instead has the pair `(19,179)` at native control 166. Entry 30 implements a different block. The incorrect binding can generate a source-consistent tree whose compiled physical machine fails its first exposed copyH instruction.

The audit also found that fully expanded copies can leave controls 12 and 166 unreachable. Charging a constant fixed budget obscured this fact. The corrected model handles both issues. See `macro_audit.md`, `macro_audit.json`, and `audit/scorer_correction.patch` for independently inspected pair identities, incoming-history conditions, and the code change. The validated delivered gate-reassociated 194-state machine keeps copyH atomic and does not use the incorrect binding.

`audit/rejected/` retains three apparent 193-state tables produced with the bad binding, their exact source grammars, folds, and checker receipts. Two fail at source site 389 after 513 completed scalar outcomes; the GDH example fails at site 95 after 129 completed outcomes. The H example includes a symbolic rejection trace and a literal all-zero-register trace returning to dispatch with the wrong code tape. This rejects the advertised implementation contract; it is not a proof of any absolute halting or non-halting assertion about those tables.

The historical principal searches generated 13,446,433 proposals, and the seven additional-family searches generated 12,633,111 proposals. Their nominal scores are retained only as records of exploratory work. Five principal runs and all seven family runs included the invalid exposed-copyH model. The two head-permutation runs did not expose copyH, so that particular error was dormant in those seeds. The extra deep-gate run is additionally incomplete because exposed `node145` and `node147` require an incoming history bit of one. No result from that run is asserted as a valid physical construction.

The old executables are not supplied. Historical source, inputs, and logs are in `legacy/`, with additional-family snapshots in `compositions/`. They must not be used as a substitute for the corrected model.

## Initial source-family compositions and the deterministic tail screen

`check_initial_compositions.py` replays exact source instruction-list equality for the initial ORH, AX11HMP, QAX11H, H5X/JH5X, and symmetric H5XS/JH5XS gate exposures. It also replays their matching-bound initial cost counts. Those initial trees retain copyH as an atomic macro, so the source/cost comparison itself is unaffected by the later search error. This check does not assert their complete physical correctness.

```sh
python check_initial_compositions.py
```

`tail_gate_search.py` regenerates 3,238 admissible Catalan reassociations of the final five through ten macro leaves of the relevant AX suffix. It imports only the package's frozen construction helper and reads the delivered raw machine/source tree. Its generated template file was reproduced byte for byte; the SHA-256 is `c7fda408116613e0e3763b030ff46b041e8ebf920c05f4abcd6217d5201c812d`. The tail family does not expose copyH. Repricing it with the corrected model again gives best effective cost 62, or 195 controls.

```sh
python tail_gate_search.py tail_templates
./corrected/search tail_templates/seeds.txt corrected/leaf_attrs.txt replay_tail 0 18112300 0
```

The corrected tail receipt is `corrected_repricing/tail_reprice.log`. Zero stochastic proposals are required because the input pool itself contains every retained tail shape.

## Provenance and limits

The base annealer and compiler geometry derive from the attributed ORH research packet at the pinned ProveIt revision. Upstream notices are preserved in `../../licenses`. This investigation adds gate exposure, broader fold pricing, reachability-aware corrections, audit witnesses, and the final composition experiments.

The negative results cover these finite searches and sufficient local checks. They do not show that every 193-state PA-consistency machine is impossible. The arithmetic calibration and incomplete Lean formalization retain the scope stated in the main report.
