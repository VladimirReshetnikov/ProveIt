# Reproduce batch 163

Placement `47507759e7` preserves 1,190 ancillary files from 1,260 delivered payloads. The [mapping](data/intake-163-placement.json) also records 70 archive-only files. Recover the original nested packages to a new directory outside the checkout:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover_163.py \
  --repo "$PWD" --output /tmp/zfc-batch163-recovered
```

The helper restores four roots:

- `/tmp/zfc-batch163-recovered/64-below246/zfc-below246-research-20261018`
- `/tmp/zfc-batch163-recovered/65-beyond246/zfc-beyond246`
- `/tmp/zfc-batch163-recovered/66-below246-v2/zfc-below246-research`
- `/tmp/zfc-batch163-recovered/67-under246/zfc-under246-research-20261018`

Optional `--source 64`, `65`, `66` or `67` restores just one. Recovery uses committed arrival archives and checks every selected placed payload directly against its original archive member. It runs no proof, compiler, test or search and interprets no checksum manifest. Original `.log` names and all nested source paths are restored. Fresh [recovery validation](data/intake-163-recovery.json) passed for all 1,260 files and 1,190 placed/original pairs.

Run substantive checks on further new writable copies, because supplied scripts refresh outputs. The reviewed helpers below create those copies themselves, preserve logs and fail on a nonzero exit. Assertions must remain enabled. No C++ compiler, proof compiler, solver, external package or network request is needed for these jobs.

## Source 64

```sh
env -u PYTHONOPTIMIZE python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/replay_163_sources64_65.py \
  --source 64 \
  --package /tmp/zfc-batch163-recovered/64-below246/zfc-below246-research-20261018 \
  --output /tmp/zfc-source64-replayed
```

All ten reviewed jobs freshly passed in 6.622 seconds combined. They check the baseline macro dependencies, partial 245/244-state contracts and counterexamples, detector caller partition, two SAT models, and alternate 246-state support/all 8,391 cases/whole-tape startup. No new solver or discovery search is run. The result remains ordinary symbolic and finite evidence, not a Lean endpoint.

## Source 65

```sh
env -u PYTHONOPTIMIZE python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/replay_163_sources64_65.py \
  --source 65 --replay-ledger \
  --package /tmp/zfc-batch163-recovered/65-beyond246/zfc-beyond246 \
  --output /tmp/zfc-source65-replayed
```

All five jobs freshly passed in 95.755 seconds combined. They include 130,872 saved first-failure replays, the two strengthened prepared-frame witnesses and product/relational invariant closure. Omitting `--replay-ledger` still checks saved domain coverage, but must not be described as freshly replaying every recorded failure. The 44-million-recipe C++ search and solver UNSAT statuses are not rerun.

The root wrappers contain checksum-manifest passes and are bypassed. Source 65's context checker also has a nested checksum loop; the helper makes a separate sibling adapter that omits only that loop and corrects its status text, retaining all mathematical assertions and the original checker unchanged. `audit/README.md` has stale `portable/` paths; actual witness entry points are under `audit/`.

## Source 66

```sh
env -u PYTHONOPTIMIZE python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/replay_163_source66.py \
  --full-symbolic \
  --package /tmp/zfc-batch163-recovered/66-below246-v2/zfc-below246-research \
  --output /tmp/zfc-source66-replayed
```

The first seven jobs freshly pass in 2.757 seconds combined. The eighth job times out with exit 124 after 360.531 seconds at its explicit 360-second cap. Its stdout and stderr are empty; the checker only prints and writes its final result after completing all cases, so no partial completed-case count is available. The copied `results/full-symbolic-results.json` is byte-identical to delivery and remains inherited evidence. The frozen replay record's `full_symbolic_replayed=true` indicates that mode was requested and attempted; its terminal `FAIL` and exit 124 determine the outcome.

Seven jobs have 120-second caps; the explicitly selected complete symbolic replay has 360 seconds, based on its delivered 237-second observation. The latter aims to check 8,385 admitted arbitrary-size cases with exposed primary registers. Without `--full-symbolic`, the seven certificate/witness jobs run and the complete symbolic result remains inherited. The local core's three-step trap and the grammar candidate's bounded runtime rejection are expected verified findings, not accepted state reductions. The timeout does not refute a mathematical claim; it is preserved without a larger-limit rerun.

Even delivered `code/reproduce.py --skip-integrity` still invokes the nested checksum wrapper; the reviewed helper uses substantive jobs directly. It runs no grammar annealing, C++ search or SMT synthesis.

## Source 67

```sh
env -u PYTHONOPTIMIZE python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/replay_163_source67.py \
  --package /tmp/zfc-batch163-recovered/67-under246/zfc-under246-research-20261018 \
  --output /tmp/zfc-source67-replayed
```

All eight jobs freshly pass in 17.291 seconds combined. The helper creates a complete writable package copy and decompresses the incoming-action ledger there. It invokes eight independently source-reviewed jobs directly, each with a 120-second cap, and compares the regenerated alternate 246-state canonical table byte-for-byte with the primary supplied table. It skips the top-level delivery-manifest check and optional prior nine-job suite. All fixed source/table bindings inside the substantive checks remain enabled. Every original working-copy payload matches delivery except the elapsed-time field in the alternate-table verification JSON; the pristine extraction remains unchanged.

The jobs cover the 201-node source bisimulation, the different 202-node source's alternate 246-state machine certificate, incoming-action partition coverage, dirty-root invariant closure, a propositional countermodel and two literal counterexamples. The final job checks the three-row synthesis partition and replays all 19,661 saved affine rejection leaves. Its 952,763,904 assignments differ from the 42,486,984-assignment incoming-action family, for which only disjoint coverage is checked. Finite affine rejection is not a proof of general TM failure. Discovery, SMT synthesis and optional commutation campaigns are not rerun.

All observed runtimes are measurements, not mathematical premises. Finite fuel or dispatcher-visit rejections remain bounded. Source-program bisimulation, abstract grammar validation and a matching blank prefix do not independently establish a new binary-machine equivalence.
