# Recent-commit inspection at pinned HEAD

- Repository: `VladimirReshetnikov/ProveIt`.
- Base reviewed pin: `b310142330df89e48413c8fce62e7de223e1c7d5`.
- Current pin: `22e020937caa81d0cb72a4f63071d6c0bcc1eba9` (2026-10-26 16:54:45 UTC).
- The comparison contains 27 commits; merges mean these are a DAG difference, not a linear date window.
- Authoritative untruncated recursive Lean trees: 574 old files, 608 current files; 34 added, 32 modified, none removed. These are all `.lean` files.
- Current source materialization: 860 files; 782 reused only after matching the current Git blob SHA, 78 freshly fetched at the pinned commit; zero byte-integrity failures.
- Five directly imported BusyBeaver source dependencies are separately stored under `dependencies/`, with a verified dependency manifest.

## Coverage and evidence limits

- GitHub compare returned exactly 300 changed repository files. This is a capped repository-wide result, not evidence of complete repository change coverage.
- Active Lean coverage does not rely on that cap: `active_tree_delta.json` compares all paths and blob SHAs from both full Lean trees. `active_delta_crosscheck.json` confirms its exact 66-path match with the active Lean entries in the compare response.
- `source_manifest.json` records the selected 860-file source inventory and hashes; `verify_snapshot.py` replays byte verification. This is not a full repository checkout or dependency closure.
- Source materialization and static inspection only. This study did not run Lean/Lake, install tools, change the repository, or repeat upstream build claims as our own.

## Observed changes versus the virtual baseline

The following are observed in the pinned source delta, not merely assumed:

- `CompilerSupport.lean` is newly checked in (36 lines); DAGQuartic, NaturalDAGQuartic and QuadraticRegisterSystem delegate finite-residual proof facts to it.
- `TotalDegreeBound.lean` is newly checked in (120 lines); the ShortSystem, ShortFrontier and ShortReducedStrong modules replace large generated degree certificates with the new total-degree tactic.
- NativeArithmetic52 and the population/coefficient, Pell, polynomial/positive-domain, primitive-recursion, assignment-transport, annotated list-lookup, weak-cap and mask-support families have committed proof-body reductions.
- Sixteen new machine/tiling semantic modules and sixteen paired Checks modules are added. They are new material for the present study, not simplification proposals already implemented by this study.

The user also asks us to assume all previous proposals are applied. That is a separate counterfactual nonduplication baseline: do not infer that every archived/incoming proposal was actually integrated. The current review document reports selected upstream compilation checks; those are attributed upstream reports, not locally reproduced validation.

## New source pairs

- `CompilerSupport.lean` (shared helper/tactic)
- `DecimalMachineInitialization.lean` + paired `Checks` module
- `TotalDegreeBound.lean` (shared helper/tactic)
- `WangMachineAction.lean` + paired `Checks` module
- `WangMachineEncoding.lean` + paired `Checks` module
- `WangMachineStep.lean` + paired `Checks` module
- `WangMachineTraceBounds.lean` + paired `Checks` module
- `WangTiles942HeadBounds.lean` + paired `Checks` module
- `WangTiles942InitialStrip.lean` + paired `Checks` module
- `WangTiles942InputLanguage.lean` + paired `Checks` module
- `WangTiles942OperatingRow.lean` + paired `Checks` module
- `WangTiles942ResetHorizontal.lean` + paired `Checks` module
- `WangTiles942ResetRows.lean` + paired `Checks` module
- `WangTiles942RowEncoding.lean` + paired `Checks` module
- `WangTiles942RowStep.lean` + paired `Checks` module
- `WangTiles942Signals.lean` + paired `Checks` module
- `WangTiles942StepConstruction.lean` + paired `Checks` module
- `WangTiles942StripGeometry.lean` + paired `Checks` module

## All modified active modules

- `DiophantineConsistency.lean`: 297 → 313 physical lines (+16).
- `DiophantineConsistency/AnnotatedAssumption.lean`: 108 → 97 physical lines (-11).
- `DiophantineConsistency/AnnotatedBound.lean`: 330 → 325 physical lines (-5).
- `DiophantineConsistency/AnnotatedProofChecker.lean`: 388 → 380 physical lines (-8).
- `DiophantineConsistency/AnnotatedRename.lean`: 374 → 369 physical lines (-5).
- `DiophantineConsistency/AnnotatedRuleSide.lean`: 86 → 75 physical lines (-11).
- `DiophantineConsistency/DAGQuartic.lean`: 285 → 257 physical lines (-28).
- `DiophantineConsistency/GapWordBounds66.lean`: 261 → 254 physical lines (-7).
- `DiophantineConsistency/LowMaskCoding.lean`: 405 → 395 physical lines (-10).
- `DiophantineConsistency/MaskPopulation.lean`: 162 → 155 physical lines (-7).
- `DiophantineConsistency/MultiTargetCarry.lean`: 273 → 263 physical lines (-10).
- `DiophantineConsistency/NativeArithmetic52.lean`: 422 → 376 physical lines (-46).
- `DiophantineConsistency/NativeMaskPopulation.lean`: 110 → 96 physical lines (-14).
- `DiophantineConsistency/NativePellBootstrap.lean`: 685 → 671 physical lines (-14).
- `DiophantineConsistency/NativePellFirstIndex.lean`: 108 → 104 physical lines (-4).
- `DiophantineConsistency/NativePellPower.lean`: 181 → 180 physical lines (-1).
- `DiophantineConsistency/NativePellStepDown.lean`: 248 → 230 physical lines (-18).
- `DiophantineConsistency/NaturalDAGQuartic.lean`: 293 → 264 physical lines (-29).
- `DiophantineConsistency/PRCode.lean`: 115 → 105 physical lines (-10).
- `DiophantineConsistency/Polynomial.lean`: 125 → 116 physical lines (-9).
- `DiophantineConsistency/PositiveDomain.lean`: 34 → 32 physical lines (-2).
- `DiophantineConsistency/QuadraticRegisterSystem.lean`: 170 → 158 physical lines (-12).
- `DiophantineConsistency/QuarticCompiler.lean`: 449 → 448 physical lines (-1).
- `DiophantineConsistency/Representation.lean`: 260 → 235 physical lines (-25).
- `DiophantineConsistency/ScalarPRCode.lean`: 87 → 76 physical lines (-11).
- `DiophantineConsistency/ScalarPROptimizer.lean`: 153 → 140 physical lines (-13).
- `DiophantineConsistency/SelectiveCoefficientBounds.lean`: 234 → 211 physical lines (-23).
- `DiophantineConsistency/ShortFrontier.lean`: 503 → 223 physical lines (-280).
- `DiophantineConsistency/ShortReducedStrong.lean`: 565 → 232 physical lines (-333).
- `DiophantineConsistency/ShortSystem.lean`: 1117 → 558 physical lines (-559).
- `DiophantineConsistency/SplitCoefficientBounds.lean`: 122 → 117 physical lines (-5).
- `DiophantineConsistency/SplitWordBounds.lean`: 376 → 369 physical lines (-7).

## Complete commit difference

| Commit | UTC time | Subject |
|---|---|---|
| [`72d3198bbfe1`](https://github.com/VladimirReshetnikov/ProveIt/commit/72d3198bbfe1bad124371795ed0eb5ba6b34e832) | 2026-10-26T16:16:26Z | Derive finite initialization strip walls and exact horizontal reset alternatives |
| [`076b953e7717`](https://github.com/VladimirReshetnikov/ProveIt/commit/076b953e7717a87744e94694cb34603f35c05dce) | 2026-10-26T16:17:26Z | Derive fixed strip walls and a seam-free interior through all integer times |
| [`7fa06d530df5`](https://github.com/VladimirReshetnikov/ProveIt/commit/7fa06d530df54d4aeb2e18027409df082234c69e) | 2026-10-26T16:23:03Z | Proof simplification proposal(s) |
| [`04aae514c462`](https://github.com/VladimirReshetnikov/ProveIt/commit/04aae514c4629a643c7a0bf8b36a6548a09d7b0d) | 2026-10-26T16:24:20Z | Place five more DiophantineConsistency Lean proof-simplification packets |
| [`90a2ded65d09`](https://github.com/VladimirReshetnikov/ProveIt/commit/90a2ded65d09cb88a29b89a60b6752c56d6c7d1d) | 2026-10-26T16:25:06Z | Bind the actual first machine step and exact configuration color semantics |
| [`d163c476db9c`](https://github.com/VladimirReshetnikov/ProveIt/commit/d163c476db9ca1142d2d73de8fa64c0b2c03a848) | 2026-10-26T16:30:05Z | Merge origin/main with five additional archived proof-simplification packets |
| [`edf3a19d0cc5`](https://github.com/VladimirReshetnikov/ProveIt/commit/edf3a19d0cc57787c078d344015a91bebac38c2a) | 2026-10-26T16:33:00Z | Decode exact tile inputs and derive uniform finish rows from one event |
| [`218631436cd4`](https://github.com/VladimirReshetnikov/ProveIt/commit/218631436cd407e7ce79b817ccb744764c4acb09) | 2026-10-26T16:33:51Z | Identify the actual clock1 row and rule out premature finishes in operating rows |
| [`e51476d83627`](https://github.com/VladimirReshetnikov/ProveIt/commit/e51476d83627303d8271ba906ca91b79e43e14cc) | 2026-10-26T16:34:43Z | Reuse general population and coefficient bounds in Lean proofs |
| [`124c301e580a`](https://github.com/VladimirReshetnikov/ProveIt/commit/124c301e580abfdeea6834bef63414d3a42d68d4) | 2026-10-26T16:35:22Z | Simplify polynomial specialization and positive-domain proof transport |
| [`fabda5ad5830`](https://github.com/VladimirReshetnikov/ProveIt/commit/fabda5ad5830d68123db9ed86c2b6fa424815366) | 2026-10-26T16:35:49Z | Simplify Pell sign, divisibility and bootstrap bound proofs |
| [`4c9fdf276083`](https://github.com/VladimirReshetnikov/ProveIt/commit/4c9fdf27608347bedca4c2fbecca9d86bcfb9e85) | 2026-10-26T16:35:56Z | Gather the six Lean proof-simplification packets in one directory |
| [`58971c080fb2`](https://github.com/VladimirReshetnikov/ProveIt/commit/58971c080fb2308fda7cc021c5486635409fd497) | 2026-10-26T16:36:39Z | Merge remote-tracking branch 'origin/main' |
| [`0fe0cb9029e9`](https://github.com/VladimirReshetnikov/ProveIt/commit/0fe0cb9029e98ec24e3d1bda005f8577b234a8f7) | 2026-10-26T16:37:23Z | Reuse supplied equations under primitive recursion in correctness proofs |
| [`dc055c5026f9`](https://github.com/VladimirReshetnikov/ProveIt/commit/dc055c5026f91997b8cd47f3711149d9a865a28b) | 2026-10-26T16:37:51Z | Replace the generated Short* degree certificates by a total-degree tactic |
| [`9bd29079d5e1`](https://github.com/VladimirReshetnikov/ProveIt/commit/9bd29079d5e1c6cc1c0bcaee6cb57d59b835cba9) | 2026-10-26T16:39:03Z | Proof simplification proposal(s) |
| [`3a1fa28491e6`](https://github.com/VladimirReshetnikov/ProveIt/commit/3a1fa28491e67afe7aad989ec8e073ad3be338cd) | 2026-10-26T16:39:05Z | Share natural assignment transport across representation constructors |
| [`993d6730a283`](https://github.com/VladimirReshetnikov/ProveIt/commit/993d6730a283f78b6b92cb197abc3b5200faa003) | 2026-10-26T16:39:11Z | Bind operational color updates to actual transition signals and receiver targets |
| [`c327aa8c6c5e`](https://github.com/VladimirReshetnikov/ProveIt/commit/c327aa8c6c5e36a171b695d10b7441fb8261cddb) | 2026-10-26T16:41:16Z | Reuse core list lookup lemmas in annotated checker proofs |
| [`6f46a5e3480a`](https://github.com/VladimirReshetnikov/ProveIt/commit/6f46a5e3480a2fa2e45993b8090826f256aeaa56) | 2026-10-26T16:43:16Z | Merge current main and reconcile proof-simplification adoption records |
| [`04267333bd04`](https://github.com/VladimirReshetnikov/ProveIt/commit/04267333bd0424603bc8fba043bf7944d1e53c54) | 2026-10-26T16:47:59Z | Prove strict Wang-strip head containment and sharp actual trace bounds |
| [`a421ec86eb86`](https://github.com/VladimirReshetnikov/ProveIt/commit/a421ec86eb86377f62fe9dd2d807561bcae8ddc2) | 2026-10-26T16:49:01Z | Prove actual Wang row evolution and construct its reverse step row |
| [`4b3dd4efb10f`](https://github.com/VladimirReshetnikov/ProveIt/commit/4b3dd4efb10f1af27143a6142380322131968726) | 2026-10-26T16:51:48Z | Merge origin/main proof simplifications and archive consolidation |
| [`7df66a39fcfb`](https://github.com/VladimirReshetnikov/ProveIt/commit/7df66a39fcfb330ca55f526ff892b8cac5dcbce6) | 2026-10-26T16:52:41Z | Reuse unconditional word bounds in weak-cap packing proofs |
| [`7ac31d169ef5`](https://github.com/VladimirReshetnikov/ProveIt/commit/7ac31d169ef5d5fc1230425f8573b3d47ec98d84) | 2026-10-26T16:53:14Z | Simplify support sums and predecessor powers in mask proofs |
| [`b9becb35383d`](https://github.com/VladimirReshetnikov/ProveIt/commit/b9becb35383d96972854d28cb1fbe9dbced14a3f) | 2026-10-26T16:54:00Z | Share finite residual proofs across the circuit compilers |
| [`22e020937caa`](https://github.com/VladimirReshetnikov/ProveIt/commit/22e020937caa81d0cb72a4f63071d6c0bcc1eba9) | 2026-10-26T16:54:45Z | Merge commit '4b3dd4efb10f1af27143a6142380322131968726' into codex/zfc-diophantine-consistency |

## Key source anchors

- Current adoption review: `sources/Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261026-root.md`.
- Current module-level review notes for the Wang additions are in the same reviews directory.
- All current active source files: `sources/Computability/DiophantineConsistency/Lean/`.
- Root configuration: `sources/lakefile.toml`, `sources/lake-manifest.json`, `sources/lean-toolchain`.
