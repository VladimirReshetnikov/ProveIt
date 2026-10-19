# Consistency calibration of the rotated 240-state register source

[`CalibratedRotation240`](../../Lean/BusyBeaver/ZFC/CalibratedRotation240.lean)
proves that the rotated register program, started at `LogicalSeed246.initial`,
halts exactly when ZF has a refutation, and exactly when ZFC has a refutation.
Its nonhalting is therefore equivalent to the corresponding consistency
statements. These are external Lean theorems about the register program.

The proof composes the checked
[source rotation](source_rotation240.md) with `CalibratedRotation244`.
Its program comparison quantifies over every initial register function,
including registers beyond the nine primary fields. The existing logical
seed then supplies the native-theory, ZF and ZFC calibrations.

The [actual check](results/calibrated-rotation240-verification.json) passes
seven named theorem probes and nine typed callers with zero warnings.
Source and audit took 0.295 and 0.279 seconds. They shared a 120-second
deadline with one thread, 4,096 MiB and default proof limits. Exactly 200
project modules and Init were selected from the two successful parent records.
The audit reports only `propext`, `Classical.choice` and `Quot.sound`.

The [publication record](results/calibrated-rotation240-publication.json),
[original guard and audit](calibrated-rotation240/), and
[lossless text history](calibrated-rotation240/history.json.gz) preserve the
successful bytes, preparation and raw logs. The guard retains historical
scratch/provider paths; publication performed no proof replay or dependency
build.

For the literal 240-state binary machine, this calibration must still be
composed with complete decoder coverage, the
[runtime proof](rotation240_runtime.md), and the
[checked startup frame](rotation240_tree_frame.md). Its internal PA theorem
remains a separate obligation. Attribution follows the imported Mira-Cult,
Jeff Ketchersid, Andrew James Wade and ProveIt constructions.
