# Shifted-source bound validation

Source commit `726bb505a9d4eede15d6fe3bd4561a9f0535b95f`, parent `2745bd77e06ecfbbb9b9523e4fc2e067978d4cef`. In `NativeShiftedSourceAdapter.source_old_z_gt_one`, deriving positivity of the product directly and extracting positivity of its left factor removes two net lines, with no change to imports, definitions, theorem statement or assumptions. The previous proof is attributed to `00f12370c1d`; no Claude coauthor is claimed. The parent and commit target sources match the tested baseline and final snapshots, respectively: SHA-256 `e2dfeee74998ee0be6275743871c64c4e70eb3f39165bb0aafdbad377d32379e` / `1e33f29a1c8e1856766779286168f8abbaf9b0d44a95c85b3ddcf82a242d35f7`.

Paired source-ordered target and sole tracked Lean-project direct client `NativeShiftedSourceAdapterChecks` builds passed in the initial and refreshed lanes (eight builds). Target logs are empty; the check logs print the same axiom reports. Baseline / final compiled-object SHA-256 values, identical between the initial and refreshed lanes within each phase:

- `NativeShiftedSourceAdapter`: `d20bbb03a57def0b05db980d467a934e4a10241de88cc27cbcffb32781981c1c` / `a0abbcf5248734c37dc06212f2acc88a97dbd7b6be5e60b355d127e3f4754be6`.
- `NativeShiftedSourceAdapterChecks`: `79173c8fd30750685178b1eee8e6d7416e6d96f5061d156c95eef65db3f4ad16` in both phases; client source SHA-256 `d89941394413efb2761a30a18dbc83ddace1dbe44d2670f0675cfc15c4c67773`.

Eight probes pin the target and both direct provider objects before and after execution. The baseline has 32 target-namespace declarations and final has 31: generated `source_old_z_gt_one._proof_3` disappears, and generated `source_old_z_gt_one._proof_2` has a changed type/axiom report. The other 30 common reports match. Default simp and instance probe logs are byte-identical. These observations do not cover all proof bodies or persistent extensions. A search of 90,633 tracked and nonignored untracked Lean/Python files found no references to the two affected generated names.

Refreshed direct project inputs have source/object SHA-256 pairs linked to successful source-current producer receipts:

- `NativeOrdinarySourceConstruction`: source `b40f896c329a6d93825beb396321bc558e19b3ea18275124f91e367fd0a0afda`, object `e93a1373d407c2dd56d7c452db6a1cc45fd2e3b65b420716ab5d1bca22fdfbea`; `/dev/shm/beta-int-sharing/replay-final-records.json`.
- `NativeQuadraticParent`: source `ae7168209b3823a8e8eeb57382a6ffe862dfee2d24e0b5d3dfac72ea16921e0a`, object `b459195f9546fe9f79dfa7e2135c3be8d641388a5f57662238b75046d0c5279b`; `/dev/shm/native-row-sharing/v3-repeat-final-records.json`.

A separate review snapshot also imports the target and was not rebuilt. The initial quadratic-parent object had no matching source-current producer receipt; the refreshed replay resolves that direct-provider boundary. Other project, Foundation and Mathlib transitive inputs remain cached; no complete current-source closure is claimed. Final client direct-input source paths sampled the pre-adoption workspace while target builds separately connect each phase object to its tested source snapshot.

Temporary evidence may not persist; SHA-256 values follow. Full replay requires the transient records, build environment and excluded compiled objects. Raw logs and compiled objects are not included here.

- `/dev/shm/native-z-positive-142/baseline-records.json`: `9b7c05d2e7efd93f4c211d20f16411018088ba4069b60399b5f6f268006b785f`.
- `/dev/shm/native-z-positive-142/final-records.json`: `cbad810e2244095813637332b85a30280eade57c0415d23ccb5ce18c875f653a`.
- `/dev/shm/native-z-positive-142/baseline-refresh-records.json`: `95d77c2468ff6498bf64e3beb0cfeb8731b9751874d4ff4a16c3b2b957b1e6d3`.
- `/dev/shm/native-z-positive-142/final-refresh-records.json`: `f48617e3600997287f0336c242e56f190bc7c36ab70e15066be86fd6e0ae32b5`.
- `/dev/shm/native-z-positive-142/probe-records.json`: `21eefe86e4cdbf64682df5b89eab3fa26f85273a5b91dd504ec8a516dcf88123`.
- `/dev/shm/native-z-positive-142/reference-search.json`: `2dd7bef06ff5cccd993e8c0dcea37bbf5b2468a254c5288b817f3abdb5ec086d`.
- `/dev/shm/native-z-positive-142/audit.py`: `4f0668e7412cb5e940428882a57f17297e05178e489d75c1e1b33db5c40d9b6f`.
- `/dev/shm/native-z-positive-142/audit.log`: `98bd5585f4b8828d2b0fa2b48ac9e7c572455a201639606e493f28f123cdbdb5`.
- `/dev/shm/beta-int-sharing/replay-final-records.json`: `c5d0e2b9f7b23abee3b3a8ef8d04db1b1f16f32fca58d4002a52805f9dec7ba5`.
- `/dev/shm/native-row-sharing/v3-repeat-final-records.json`: `0e8bfd96ef3cc63399f3ed4b0b3e553711c5a82f0779696742a0c60d8e039e52`.
- `/tmp/native-z-positive-peer-143.py`: `4207645db3d7f171126c5eb7861bb7da13d2b4fd9eba2ee31369954e189b86f0`.
- `/tmp/native-z-positive-peer-143-review.txt`: `e781e834a8f006ab5f9a5a3a1602e342c390098b8ff2ccf2a7e475f305439945`.

Independent review checked the mathematical step, all eight build receipts, first-path resolution, direct-provider links and probes; it separately repeated the worktree search and verified the committed and parent sources against the tested snapshots. The reviewer found no issues. The search does not cover external repositories or compiled binary consumers.
