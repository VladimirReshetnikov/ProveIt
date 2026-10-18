# Batch 165: recovery and executable checks

Use Python 3.10 or newer, with assertions enabled. All commands below use only the standard library; no network or proof compiler is required. The [placement map](data/intake-165-placement.json) records every original nested path and its flattened source-69 name. The delivered code remains unchanged, so recover those nested names before running it.

From the repository root, recover a new outside-repository directory:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover_165.py \
  --repo "$PWD" --output /tmp/zfc-source69-recovered
```

Recovery reads the original committed archive at `36633bfe16c90d9db1a8ab4b5cb35241da4b31ca`, restores all 466 files, and compares all 454 placed ancillary byte strings. It runs no verification suite. The package root is `/tmp/zfc-source69-recovered/zfc-sub246-research-20261018`. The 12 archive-only files include the main report, PDFs, TeX fragments and top-level delivery READMEs; they are recovered too.

Make a separate complete disposable copy of that package for each attempt. Keep the recovered original unchanged. The main suite writes result records, logs and `code/source-exactroot-affine-verification.json`; it makes a further temporary copy for its reference checks. From the disposable package root:

```sh
python3 -B code/verify_all.py
```

Root's recorded run passed 14 named jobs in 36.176 seconds with a 180-second process-group limit. This checks the original 246 reference, new numeric invariants, source-block/workspace/arithmetic baselines and controls, exact rejection witnesses, and stored-domain identity. The last item is a comparison of six recorded searches, not a fresh replay of those searches.

To cover the rest of the preserved reference suite, run these from `reference/context246` inside disposable copies. Root used a fresh complete package copy for each command, with a 120-second process-group bound:

```sh
python3 -B code/rebuild_machines.py --check
python3 -B code/render_table.py --check
python3 -B code/check_literal_instructions.py --program sources/Prog254.v --table machine/zfc_prefix246_old.tm --output results/literal-instructions.json
python3 -B code/check_local_contracts.py
python3 -B code/check_prefix_boxes.py
python3 -B reviews/audit246.py reviews/prior250
python3 -B code/independent_rebuild.py --baseline sources/prefix250_old.tm --output review-rebuilt246
```

The `render_table --check` command compares delivered text; it does not invoke TeX. Check that `review-rebuilt246/zfc_fold246_old.tm` is byte-identical to `machine/zfc_prefix246_old.tm`, and that `review-rebuilt246/zfc_fold246.tm` is byte-identical to `machine/zfc_prefix246.tm`.

The eighth supplement runs from the disposable package root:

```sh
python3 -B search/context/recompile_decoder.py --output results/recomputed-emitter-baseline.json
```

Explicitly require JSON fields `decoder_nodes = 203`, `states = 246`, `cases = 8391` and `failures = []`. The program can exit successfully while reporting candidate failures, so exit status alone is insufficient. This baseline is an initialized runtime check, not a new blank-start construction.

All eight supplements passed in the recorded intake. Exact commands, individual durations, raw-log locations, write locations and postchecks are in the [execution plan](data/intake-165-execution-plan.json) and [root supplemental record](data/intake-165-source69-supplemental-execution.json). Clear `PYTHONOPTIMIZE` and unrelated `PYTHONPATH` entries, retain `-B`, save stdout/stderr and terminal status, and do not run a supplied command from the immutable delivery tree.

Do not run the delivery-integrity-only `reference/context246/code/check_hashes.py` or `make integrity`; checksum manifests and line endings are outside intake work. The [optional-search instructions](69-blocks-search-README.md) describe separate finite searches, some requiring C++17. Their expensive ledgers were not rerun by this intake and are not included in the 14-plus-eight result. No new Lean/Rocq endpoint or PA proof is inferred from these executions.

The separate reintroduced source-68 archive is an exact duplicate and receives no new local number. Its original arrival and all 273 original ancillary placement bindings are retained in [the duplicate-history record](data/intake-165-history-matches.json); use the existing [batch 164 recovery instructions](intake-164-reproduction.md) for that package.
