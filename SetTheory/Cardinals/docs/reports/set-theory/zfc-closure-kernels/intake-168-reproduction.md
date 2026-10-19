# Batch 168 recovery and substantive replay

Placement `696c150e84` retains 151 ancillary files and the exact [outer-member map](data/intake168-placement.json). Twelve main-manuscript, PDF and delivery-README members remain archive-only. Both original archives are recoverable from arrival `8c41b1fb7d7bb8cd0612e37848181fe4a2f5d569`, including their original names. The nested 242 ZIP in Source 73 is an exact copy of the separate Source 72 arrival, not another placement.

From the repository root, create a new directory outside it and recover the ZIPs:

```bash
mkdir /tmp/zfc-intake168-original
git show 8c41b1fb7d7bb8cd0612e37848181fe4a2f5d569:docs/incoming/BusyBeaver_242_Research_2026-10-18.zip > /tmp/zfc-intake168-original/BusyBeaver_242_Research_2026-10-18.zip
git show 8c41b1fb7d7bb8cd0612e37848181fe4a2f5d569:docs/incoming/BusyBeaver_241_Companion_2026-10-18.zip > /tmp/zfc-intake168-original/BusyBeaver_241_Companion_2026-10-18.zip
python3 -m zipfile -e /tmp/zfc-intake168-original/BusyBeaver_242_Research_2026-10-18.zip /tmp/zfc-intake168-original/242
python3 -m zipfile -e /tmp/zfc-intake168-original/BusyBeaver_241_Companion_2026-10-18.zip /tmp/zfc-intake168-original/241
```

The resulting source roots are `/tmp/zfc-intake168-original/242/busybeaver242-research` and `/tmp/zfc-intake168-original/241/busybeaver241-companion`. These are original nested layouts. Do not execute flattened host scripts directly: their unchanged sibling input names refer to these layouts. Replay must use another disposable copy, preserving the pristine recovery and delivered evidence.

The [recovery helper](code/recover168.py) was read and executed by root. Its [actual result](data/intake168-recovery.json) restores all 163 original member names and compares all 151 maintained ancillary files with the committed originals, without executing delivered code. Both retired archives remain recoverable from the arrival commit.

## Actual intake replay

Root's exact runner `/tmp/zfc-intake-8c41b1fb7d/replay_root.py` uses persistent disposable copies under `fresh-replay-1/`. It invokes substantive leaf scripts directly with assertions enabled and `-B`; it does **not** invoke the delivery `verify_all.py` wrappers or validate their checksum manifests. Its 14 finite jobs cover the principal A proof, both independent three-fold proofs, all boot checks, inherited 243 table/compensation/source-frame checks, three 242 concrete jobs and four 241 proof/boot/concrete jobs.

Five full universal jobs cover 242 A, B and C, inherited 243, and primary 241, at most two concurrently. For each, the runner checks exactly 8,390 cases and compares the entire newly emitted case array and semantic summary fields with the delivered result. Timing is not a semantic comparison field. Original and fresh outputs, per-job records and separate stdout/stderr are retained.

Root's [fresh substantive replay](data/intake168-fresh-replay.json) passed all 19 jobs: 14 local/boot/concrete jobs and five complete universal jobs for 242 A, B and C, inherited 243 and primary 241. Every universal job checks 8,390 cases, with its complete emitted case array equal to the delivered array. The terminal status is `ROOT_SUBSTANTIVE_LEAF_REPLAY_PASS`. The exact executed runner, raw per-job records and stdout/stderr are preserved in [replay history](data/intake168-replay-history.json). Delivery manifest wrappers were not invoked; this replay includes no Lean, PA, TeX or discovery-search execution. The companion's delivered wrapper would inherit earlier full 242/243 runtime receipts; root's replay refreshes them as well.

The reviewed [portable adapter](code/replay168_portable.py) changes only source/output selection and fresh-output separation checks. Its mathematical functions and job body are byte-identical to the [exact executed runner](code/intake168_replay_root_original.py). From the host root:

```bash
python3 -B code/replay168_portable.py \
  --source-242 /tmp/zfc-intake168-original/242/busybeaver242-research \
  --source-241 /tmp/zfc-intake168-original/241/busybeaver241-companion \
  --output /tmp/zfc-intake168-leaf-replay
```

The portable adapter has not been executed and has no separate replay result. Root's existing replay is evidence for the unchanged substantive job body, with the exact original runner preserved. A new full replay is unnecessary merely to archive the source adaptation.

## Optional historical delivery entry points

The following commands describe the delivered suites, not the actual intake method. Run them only on disposable restored copies if their historical wrapper behavior is wanted:

```bash
python3 -B /tmp/zfc-intake168-original/242/busybeaver242-research/verify_all.py --output /tmp/zfc-intake168-historical242.json
python3 -B /tmp/zfc-intake168-original/241/busybeaver241-companion/verify_all.py --output /tmp/zfc-intake168-historical241.json
```

Those wrappers perform manifest checks, which were deliberately excluded from intake work. Their `--quick` modes skip universal jobs and cannot be reported as full runtime replays. No such wrapper was run for the actual root record described above.

See [reconciliation](intake-168.md) and the [Source 72](intake-168-source-72.md) / [Source 73](intake-168-source-73.md) dossiers for the separate mathematical and formal scopes. Only the two batch ZIPs were retired. The 26 other queued archives at placement remain outside this batch.
