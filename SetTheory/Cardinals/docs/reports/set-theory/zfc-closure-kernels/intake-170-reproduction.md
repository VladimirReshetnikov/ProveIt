# Batch 170: recovery and substantive reproduction

Placement `0841b55a14` preserves every original member. The [fresh terminal replay](data/intake170-fresh-replay.json) records all ten substantive jobs passing; the commands below reproduce those checks without running delivery-manifest checks or nested historical suites.

The original archive is preserved at `e5c2b3337e8f38a54a1dbd2ad7e8feb7d5996d6a:docs/incoming/zfc240-source-rotation-20261018.zip`. The [placement map](data/intake170-placement.json) binds all 79 original members, including six archive-only manuscript/PDF/README files and 73 ancillary occurrences resolving to 67 targets. Exact aliases do not change the recoverable original names. Restore the original wrapper and relative paths; the flattened host code/data files retain their delivered relative imports and must not be run in place.

From the repository root, recover the exact original layout and check all 73 ancillary aliases against maintained targets:

```bash
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover170.py \
  --repo "$PWD" --output /tmp/intake170-recovered
```

The [recovery helper](code/recover170.py) reads the exact committed arrival and actual placement map, rejects unsafe ZIP members, restores all 79 members under `source80/zfc240-source-rotation-20261018`, and checks the 73 ancillary occurrences against 67 maintained targets. The [actual root recovery](data/intake170-recovery.json) passes all 79/73/67 checks. It executes no delivered code. The nested 241 ZIP remains one original member, not an extra host source. The six archive-only members are recovered from Git with their original names.

The [portable replay adapter](code/replay170_portable.py) accepts only source, output and prior-record paths; its substantive body is identical to the actual root runner after the documented path substitution. From an installed repository checkout:

```bash
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/replay170_portable.py \
  --source /tmp/intake170-recovered/source80/zfc240-source-rotation-20261018 \
  --output /tmp/intake170-replay \
  --parent-record SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake168-fresh-replay.json
```

The adapter requires the exact historical parent record and creates its own fresh copy. It is supplied for reproduction; the recorded fresh execution used the preserved original root runner. No second full replay is claimed for the path-only adapter.

Copy the entire reconstructed package to a separate fresh working directory. Preserve the original extraction. Use Python 3.10 or later with assertions enabled and bytecode writes disabled. Every substantive job should have a bounded process group and persistent stdout/stderr; root's run allows 1,200 seconds per job. Clear inherited `PYTHONPATH`, set `B245_INPUTS` to the copy's `reference` directory and `B245_OUTPUT` to a fresh external output directory, matching the recorded execution environment.

| Job | Delivered entry point and substantive arguments |
| --- | --- |
| Exact construction | `build.py --output <out>/build.json` |
| First local whole-tape proof | `verification/verify_local.py --output <out>/local_root.json` |
| First startup/clock check | `verification/verify_boot.py --output <out>/boot_root.json` |
| Independent local proof | `verification/verify_local_independent.py --root <copy> --output <out>/local_independent.json` |
| Independent sparse/dense startup | `verification/verify_boot_independent.py --root <copy> --output <out>/boot_independent.json` |
| Complete source graph and rotated startup | `verification/verify_source.py --package-root <copy> --output-dir <out>/source` |
| Independent source/local review | `verification/review_independent.py --root <copy> --output <out>/review_independent.json` |
| Infinite-model corpus | `theory/dense_order_filter.py --output <out>/dense_order_results.json` |
| Full rotated 241 runtime | `verification/symbolic_runtime.py --table <copy>/reference/rotated241_old.tm --sites <copy>/machines/sites_logical.json --output <out>/rotated241.json` |
| Full final 240 runtime | `verification/symbolic_runtime.py --table <copy>/machines/zfc240_old.tm --sites <copy>/machines/sites_logical.json --output <out>/final240.json` |

Run each script from its own directory as in the root record. Both runtime calls use the unchanged delivered engine and produce a separate per-case JSON file. Their scope is arbitrary unary lengths and finite spare lists under the proved symbolic rules. The root check compares all 8,386 final per-case records with delivery, all 480 exercised rows, table/source/engine/helper identities, minimum duration and summed rule count. The [fresh terminal record](data/intake170-fresh-replay.json) records exact commands, statuses, elapsed times and persistent output bindings. Rotated 241 passes 8,386 cases/2,318,435 rules/482 rows; final 240 passes 8,386 cases/2,322,575 rules/480 rows. The startup checks reproduce 408,941 and 409,691 steps and the complete final tape. [Replay history](data/intake170-replay-history.json.gz) preserves raw logs, outputs and the executed runner; delivered timings remain separate.

The aggregate `verify_all.py` also checks delivery manifests and invokes nested predecessor quick suites. Intake intentionally uses the ten direct leaf jobs instead. The prior 241 companion is byte-identical to its `8c41b1fb7d` archive; its four copied runtime inputs and the three literal engine substitutions are checked separately by root. Earlier [batch 168 evidence](data/intake168-fresh-replay.json) remains earlier evidence. No nested historical job is relabelled fresh.

The optional theory JSON input interface is narrower than a validated general frontend: it does not strictly reject malformed constructor arities/names, and the Separation-construction helper does not enforce freshness against generated variables 2 and 3. Validate arbitrary formulas and reserve those names before using the helper. The bundled corpus uses well-formed fresh formulas. Its script's line-7 reference to `dense_order.tex` is stale; read the recovered `report/sections/theory.tex` for the supplied proof. Its finite tests do not substitute for the uniform proof of all weak-Collection instances.

Discovery programs under `search/` require C++17 for the synthesis tools and Python for domain generation. They have bounded radii, durations and proposal families; the retained negative counts are delivered research history. They are not part of the acceptance replay above. No discovery search, compiler, Lean/Rocq proof, network fetch or TeX build is required by those ten Python jobs.

The reconciliation leaves the host article/PDF untouched. The catalogue's updated manifest PDF is a separate required build. See [the main note](intake-170.md) for the distinction between the ordinary 240 candidate, the checked external compensated244 baseline and the open internal PA target.
