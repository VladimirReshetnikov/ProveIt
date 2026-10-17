# Batch 158: recover original layouts and replay substantive checks

`recover_158.py` requires Python 3.10+ and Git. It runs no tests or compiler. It reads the five committed arrival ZIPs with `git show`, rejects unsafe archive members, compares all placed ancillary files directly against the corresponding original archive payloads, and restores original nested names to a **new directory outside the repository**. No checksum-manifest records are interpreted and no line endings are converted. Manifests, where present, are opaque delivered files.

```sh
uv run --no-project --offline python -B /path/to/ProveIt/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover_158.py \
  --repo /path/to/ProveIt --output /tmp/zfc-batch158-new
```

Use `--source 51`, …, `--source 55` to recover only one package. The helper prints each exact package root and writes `recovery.json`; it refuses an existing output directory. Local 55 is the countdown report. The separately salvaged negation report is source 56/batch 159 and is deliberately absent here.

With the example output above, the roots are:

| Source | Package root |
| --- | --- |
| 51 geometric | `/tmp/zfc-batch158-new/51-geometric/zfc_gap_clock` |
| 52 roles | `/tmp/zfc-batch158-new/52-roles/zfc_sub252_research_20261017` |
| 53 span | `/tmp/zfc-batch158-new/53-span/permutation252-reduction-study` |
| 54 cache MP | `/tmp/zfc-batch158-new/54-cachemp/cachemp252-research-20261017` |
| 55 countdown | `/tmp/zfc-batch158-new/55-countdown/zfc252-reduction-research-2026-10-17` |

The recovery-only validation restored 846 original files and compared all 812 placed ancillary files successfully. The following are **separate optional replays**, using those recovered scratch packages. Some scripts rewrite their own result files, so use this recovery copy rather than placed repository files. Keep Python assertions enabled; do not use `-O`. These commands require no network or Lean/Coq build. Successful finite or symbolic checks retain the scopes stated in the individual intake reviews.

## 51: principal finite checks and complete no-filler fold census

Run from source 51's package root:

```sh
uv run --no-project --offline python -B clock_schedule.py --candidates 100000 --output data/clock_schedule_results.json
uv run --no-project --offline python -B gap_dag_audit.py --source machine/inputs/Prog254.v --output gap-dag-audit.json
uv run --no-project --offline python -B machine/code/assemble_gap_runtime.py
uv run --no-project --offline python -B experiments/no_filler_unit/check_no_filler_unit253.py --runtime-root machine --output experiments/no_filler_unit/replay
uv run --no-project --offline python -B machine/code/gap_loader.py --fold-past
uv run --no-project --offline python -B experiments/no_filler_frozen/nofiller_frozen_search.py --input-dir experiments/no_filler_frozen/inputs --output experiments/no_filler_frozen/replay --seconds 100
```

Intake repeated 300,000 candidates/374,146 commands, 8,381 geometric-runtime guards, 288 loader cases, 8,356 no-filler geometric guards, and all 55,471 frozen no-filler fold recipes/127,407 affine checks. The last command has a time budget; a slower host may stop early and must report partial coverage. The 253-state geometric runtime's 102-step inherited-start escape is a negative bootstrap certificate, not a consistency endpoint. No formal-proof rebuild is included.

## 52: source-role, seed and allocation checks

Bypass the top-level `reproduce.py` and nested `machine_reduction/replay.py` checksum wrappers. Run the substantive jobs directly. From source 52's package root:

```sh
mkdir replay
uv run --no-project --offline python -B research/logical_reduction/foundation_seed254.py --limit 65536 --upstream-seed vendor/ProveIt/Computability/BusyBeaver/Research/ZFC/safe_seed254.py --output replay/foundation-seeds.json
uv run --no-project --offline python -B research/proof_audit/verify_hf_embedding.py --max-vertices 4 --output replay/hf-embedding.json
```

For the dependent allocation pipeline, run from `research/machine_reduction/` in that same package, in this order:

```sh
uv run --no-project --offline python -B value_analysis.py 3 4 8 16 32
uv run --no-project --offline python -B freeze_allocation.py
uv run --no-project --offline python -B allocation_certificate.py
uv run --no-project --offline python -B allocated_dag.py
uv run --no-project --offline python -B compact_allocated_dag.py
uv run --no-project --offline python -B compile_controls.py ../../vendor/ProveIt
uv run --no-project --offline python -B ../proof_audit/audit_role_inputs.py --candidate-dir . --output ../../replay/role-inputs.json
uv run --no-project --offline python -B ../proof_audit/epsilon_progress_audit.py allocation-certificate.json --output ../../replay/epsilon-progress.json
uv run --no-project --offline python -B ../proof_audit/audit_compacted_control.py allocated-dag.json allocated-dag-compacted.json --output ../../replay/compacted-control.json
uv run --no-project --offline python -B affine_analysis.py
uv run --no-project --offline python -B affine_analysis.py --reduced
uv run --no-project --offline python -B coalescing_family_search.py
```

`compile_controls.py` emits and audits finite Turing tables in Python; it invokes no proof compiler. Intake checked all 232 coalescing-family choices. The larger dynamic-renaming and time-limited incoming-action explorations are separately recorded bounded searches, not prerequisites for this positive pipeline and not global lower bounds.

## 53: modular phase, semantic variants and affine codecs

Run from source 53's package root. Its wrapper requires output outside that package; the example uses a new sibling directory under the recovery output:

```sh
uv run --no-project --offline python -B reproduce.py phase --out /tmp/zfc-batch158-new/span-replay
uv run --no-project --offline python -B reproduce.py semantics --out /tmp/zfc-batch158-new/span-replay
uv run --no-project --offline python -B codecs/affine_codec_search.py --max-modulus 12 --output /tmp/zfc-batch158-new/span-replay/affine-codecs.json
```

These are the substantive modes reviewed and replayed at intake. Do not run the manifest-only `verify` mode. The historical completed/partial machine-search ledgers retain their original scopes; these commands do not repeat those searches.

## 54: default positive suite without the manifest wrapper

Use the companion `replay_158_cachemp.py`:

```sh
uv run --no-project --offline python -B /path/to/ProveIt/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/replay_158_cachemp.py \
  --package /tmp/zfc-batch158-new/54-cachemp/cachemp252-research-20261017 \
  --output /tmp/zfc-batch158-new/cachemp-positive.json
```

The adapter loads the unchanged delivered `verify.py`, replaces only its manifest-check function in memory with a no-op, and invokes its default positive suite. This preserves the source-binding, source-command, bootstrap and affine checks. It writes a new output file and changes no delivered source bytes. The intake already replayed this suite with the same in-memory adapter; this portable adapter has been prepared and source-reviewed without rerunning the suite. It does not enable optional multi-million-recipe searches.

## 55: countdown package

The top-level `verify.py --skip-manifest` still calls a nested checksum-manifest wrapper through `check_inputs`, so that switch alone does not implement the intake policy. Run these substantive jobs directly from source 55's package root:

```sh
mkdir replay
uv run --no-project --offline python -B binary_loop_experiments/verify_diagnostics.py --output replay/contracts.json
uv run --no-project --offline python -B proof_audit/binary_countdown_literal.py --output replay/literal.json
uv run --no-project --offline python -B proof_audit/check_dbm_certificate.py proof_audit/relational_dbm_threshold2.json proof_audit/relational_dbm_threshold8.json proof_audit/relational_dbm_threshold32.json proof_audit/relational_dbm_threshold128.json --output replay/dbm.json
uv run --no-project --offline python -B proof_audit/countdown_loops.py --output replay/source-loops.json
uv run --no-project --offline python -B proof_audit/check_loop_projection.py --output replay/projection.json
uv run --no-project --offline python -B binary_experiments/audit_lazy_partition.py --manifest binary_experiments/lazy_context_complete_results.json --journal binary_experiments/lazy_context_complete_nodes.jsonl --output replay/partition.json
```

The last command's `--manifest` names an experimental result/partition record, not a checksum manifest. It checks assignment accounting against the journal. Intake replayed 181 retained diagnostic positives, 16 continuous literal whole-tape controls, all four DBM certificates, 1,433 source loops and their matrix projections, and the 2,898,046-assignment lazy partition. The journal check does not repeat every rejected symbolic trace. Additional reviewer-selected target regeneration and aggregate ledger checks are recorded in the source-55 dossier; they are not required by the commands above. These replays do not repeat all historical mutation trials or establish a new complete binary machine.

None of these commands establishes a sub-252 result or completes the internal PA consistency equivalence. The report's archived formal logs remain attributed evidence unless an explicitly scoped fresh proof check is performed separately.
