# Recovering and checking the permuted216 alternatives

Run from the repository root with Python3.10 or newer. All commands below use
the standard library. Recovery restores the72 actual members from arrival
`d59b4418821c598c4703f0a60b1f7cbae4f3bcf6`; placement `607e98b59d` retired the ZIP.
It does not execute the submission or its ancestors.

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake197.py /tmp/permuted216-recovered
```

The packet is restored at
`/tmp/permuted216-recovered/K216_Permuted_Commands_2026-10-21/K216_Permuted_Commands_2026-10-21`.
The [placement map](data/intake197-placement.json) records aliases and
archive-only main manuscript/input files. Absent standalone documents and
output paths mentioned in the original source README are not fabricated.

## Read the saved actual evidence without rerunning machines

The publication keeps all new output and raw logs. Large JSON files are gzip
encoded; [archive-index.json](data/intake197-fresh/archive-index.json) binds both
stored and uncompressed bytes. Selected actual input snapshots are retained
under `saved-inputs/`; the complete pristine package remains recoverable.
Prepare a fresh audit view, then run the original unchanged read-only auditor:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake197-fresh/prepare_audit_view.py --output /tmp/permuted216-saved-view
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake197-fresh/review_saved.py --run /tmp/permuted216-saved-view --packet /tmp/permuted216-recovered/K216_Permuted_Commands_2026-10-21/K216_Permuted_Commands_2026-10-21 --output /tmp/permuted216-saved-review.json
```

Expected statuses are `EXACT_SAVED_AUDIT_VIEW_PREPARED` and
`PASS_INDEPENDENT_SAVED_OUTPUT_AUDIT`. These commands do not execute a candidate,
import its checker, compile anything or invent historical input captures.
The auditor rebases historical absolute receipt/argv paths to the saved view.
Its new output uses the same semantic checks as the original
[actual-review.json](data/intake197-fresh/actual-review.json).

The original runner did not record a historical before/after hash map. The
audit instead binds selected current actual inputs to the pristine package and
exact inherited runtime/source-helper pins. This limitation remains explicit.
Trace-row linkage is a saved-record consistency check; the two actual separate
tape replays remain the execution evidence.

## Freshly replay the ten selected leaves

Use a different fresh output directory:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake197-fresh/run.py --packet /tmp/permuted216-recovered/K216_Permuted_Commands_2026-10-21/K216_Permuted_Commands_2026-10-21 --output /tmp/permuted216-fresh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake197-fresh/review_saved.py --run /tmp/permuted216-fresh --packet /tmp/permuted216-recovered/K216_Permuted_Commands_2026-10-21/K216_Permuted_Commands_2026-10-21 --output /tmp/permuted216-fresh-review.json
```

The exact root runner and independent secondary blank driver are preserved
byte-for-byte. They copy the packet, safely extract its two pinned parent
archives as dependency data, and execute only:

1. `build_sources.py`: all four source artifacts rebuilt exactly.
2. Two `audit_command_permutation.py` runs: complete210 and120 selector/body proofs.
3. `audit_source210.py`: independent source/CFG correspondence.
4. `reconstruct.py`: both native/canonical tables rebuilt exactly.
5. `machine/audit.py`: primary canonicalization, whole blank trace and local81 lemma.
6. `audit_blank210.py` and the independent `secondary_blank.py`: full tape/trace comparisons.
7. Two pinned `validate_native.py` runs: complete quantified primitive proofs for both tables.

The eight finite processes each have a90-second cap. The two runtime processes
run in parallel with separate output directories and360-second caps. Assertions
are enabled; no delivered code is changed. Expected aggregate status is
`TEN_SELECTED_LEAVES_PASS`, followed by the independent saved-output status.
Checking process exit0 alone is insufficient: the runtime driver can return a
`NOT_PROVED` receipt without a nonzero process exit.

Expected primary/secondary figures are6,176 cases each,1,605,450/1,605,505
symbolic rules, all432 rows and minimum positive affine constants6/9. The
complete blank runs take95,674/96,244 transitions and reach the same whole
frame: native84/head−8/header57/gap1, registers `[4,0,0,0,0,0,0,0,0]`, forty
unit spares,95 one-cells and zero exterior. The original quantified phases took
162.903/161.280 seconds. Every ordered fresh case and complete startup object
equaled its delivered counterpart; timing is the only runtime-receipt change.

No wrapper, checksum manifest, ancestor proof suite, C++ compilation, broad
search or proof-assistant build belongs to this selection. Stored C++ receipts
are compared only as delivered evidence. The inherited numerical calibration
and the ordinary source compiler are separately reviewed premises. The
[intake note](intake-197.md) and [candidate proof](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k216/alternatives/permuted/proof.md)
explain their mathematical scope.
