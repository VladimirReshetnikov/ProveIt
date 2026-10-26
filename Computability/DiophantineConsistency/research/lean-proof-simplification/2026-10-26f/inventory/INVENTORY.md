# Source inventory and simplification triage

## Provenance and boundaries

- Repository: VladimirReshetnikov/ProveIt; commit `60e9c5d620c6c387d932876cfa2d9376f64ea56c`; retrieved 2026-10-26 UTC.
- The recursive repository tree was truncated. We instead resolved root tree → `Computability` tree → target tree; the target recursive tree is explicitly untruncated (40,179 entries).
- `provenance/source_manifest.json`: 944 selected blobs, each byte length and Git SHA-1 blob hash verified, with independent SHA-256. Every `.lean` in the requested target is present.
- `sources/` is an immutable focused snapshot, not a full buildable repository checkout. Local imported namespaces outside the requested subtree (`BusyBeaver`, `Diophantine`, `BoundedZFCConsistency`, `FirstOrder`) and Mathlib are not included.
- Pinned build: Lean `v4.32.0`; Mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`. Root configs are included.
- No Lean, Lake, elan, or Mathlib installation was discovered in PATH or searched standard locations. No proof was elaborated or kernel-checked during this inventory.

## Active versus archival scope

| Group | Files | Physical lines | Bytes |
|---|---:|---:|---:|
| Lean/DiophantineConsistency modules (includes named Checks/Audit modules) | 363 | 68,308 | 3,049,666 |
| Lean/DiophantineConsistency.lean umbrella | 1 | 283 | 13,956 |
| Lean/checks standalone wrappers | 182 | 5,380 | 230,179 |

Active total: **546 files, 73,971 lines, 3,293,801 bytes**.

Filename/directory role classification further separates the 363 module-directory files: **325 implementation-named files** (66,574 lines, 2,981,015 bytes), and **38 additional `*Checks`/`*Audit` files** (1,734 lines, 68,651 bytes). Combined with `Lean/checks/`, that is **220 check/audit files** (7,114 lines, 298,830 bytes). The role classifier is naming-based, not semantic; implementation-named files may still include audit commands. The `group` column remains explicitly directory-based; `role` records this refinement. Additional target `.lean`: 159 under `con-zfc-diophantine-forms/` (archived research/provenance, 2,242,830 bytes), and six under `candidates/` (inherited provenance, 18,040 bytes). Do not add these archival copies to active proof-maintenance savings.

The 363 module files contain 4,626 theorem/lemma declarations and 2,010 def/abbrev declarations by lexical regex. Twenty modules explicitly identify generation in their first 1,500 characters: together 16,053 physical lines, 13,372 nonblank lexical code lines, 1,546 theorem/lemma declarations. Header detection is conservative, not a proof that all other files are handwritten.

`GapCircuitSteps66` and `SplitCircuitSteps59` alone contribute 1,192 theorem declarations and 6,567 physical lines. This is a strong structural target, but eliminating presentation boilerplate does not eliminate DAG nodes or mathematical obligations.

## Largest active source targets

| File (pinned link) | Lines | Theorem/lemma declarations | Explicit generated header |
|---|---:|---:|---|
| [SplitCircuitSteps59.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/SplitCircuitSteps59.lean) | 3,445 | 622 | True |
| [GapCircuitSteps66.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/GapCircuitSteps66.lean) | 3,122 | 570 | True |
| [SplitCircuit59.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/SplitCircuit59.lean) | 1,286 | 36 | True |
| [SplitJointCircuit59.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/SplitJointCircuit59.lean) | 1,252 | 36 | True |
| [GapCircuit66.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/GapCircuit66.lean) | 1,226 | 36 | True |
| [ShortSystem.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/ShortSystem.lean) | 1,117 | 28 | False |
| [SplitCertificate59.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/SplitCertificate59.lean) | 866 | 50 | True |
| [SplitKernelData59.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/SplitKernelData59.lean) | 726 | 19 | True |
| [NativePellBootstrap.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativePellBootstrap.lean) | 685 | 26 | False |
| [NativeCoefficientBounds.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeCoefficientBounds.lean) | 679 | 31 | False |
| [NativeQuadraticParent.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeQuadraticParent.lean) | 661 | 27 | True |
| [GapKernelData66.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/GapKernelData66.lean) | 652 | 17 | True |
| [ShortReducedStrong.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/ShortReducedStrong.lean) | 565 | 14 | False |
| [CurrentKernel2011.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentKernel2011.lean) | 537 | 95 | False |
| [WangTiles942Data.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942Data.lean) | 527 | 50 | False |

## Repeated patterns worth addressing

1. **Generated step banks.** `GapCircuitSteps66.lean` (starting line 16) and `SplitCircuitSteps59.lean` (starting line 16) repeatedly instantiate `ArithmeticDAGSemantics.run_node_equation`. Keep one general evaluator theorem and generate only named equations actually used, or build demand-driven wrappers. Update generators, not only generated outputs; measure elaboration time and axiom dependencies.
2. **Map/evaluation transport.** Across active modules, the exact line `simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]` occurs 174 times (e.g. `GapNinePolynomial66.lean:103` onward). A semantic interpretation API or local named simp set could avoid restating each syntax constructor. Do not erase genuine ring/semiring distinctions.
3. **Coefficient-bound batches.** `NativeCoefficientBounds.lean` has 158 copies of the same `abs_le; constructor; linarith only [...]` line. `SplitKernelData59.lean` has 174 copies of a fixed `nlinarith only [...]` line. Generate uniform local tactics or prove an indexed bound for the coefficient family; preserve the finite evidence and benchmark rather than assume a large `simp_all` is faster.
4. **Finite-coordinate tables.** `NativeQuadraticPositions.lean` repeatedly opens insertion membership with the same simp list; an explicit membership specification or indexed coefficient-support representation could reduce repeated case analysis.
5. **Common modulus infrastructure.** Ten copies of a `NeZero (N * 2011)` instance proof occur across Current modules; four identical cast-to-divisibility conversions occur in `CurrentClause2011` and `CurrentReflectedGeometry2011`. A small upstream modulus API could centralize side-condition normalization.
6. **Scanner recursion scaffolding.** `AnnotatedBoundScan:158`, `AnnotatedLineScan:245`, `AnnotatedRenameScanPR:75`, and `AnnotatedAxiomContext:232` close related scanner primitive-recursion obligations using the same constructor expansion. Consider a reusable scanner-fold representation lemma before compressing tactics locally.

## Metrics method and cautions

`provenance/inventory.py` removes nested block comments, line comments, and string contents, preserves newlines, then applies lexical token/declaration patterns. It is not a Lean parser. `declaration_spans.csv` measures from a top-level-looking declaration to the next declaration and is only a triage estimate, not exact proof-body length.
Token counts in module files include 3,748 `rw`, 2,582 `simp`, 647 `simpa`, 1,659 `omega`, 682 `ring`, 557 `nlinarith`, and 3,576 `decide`; repetition is not itself evidence of poor code. No active lexical `sorry`, `axiom`, or `native_decide` token was found. This is not a transitive axiom audit or a build result.
`imports.csv` separates module and check-wrapper edges. The umbrella imports 283 modules, so broad umbrella imports can hide unnecessary dependencies in small check files. Any reduction must preserve the full intended audit coverage.

## Supporting files

- `inventory/summary.json`: scope-aware totals and token frequencies.
- `inventory/modules.csv`: per-file metrics and SHA-256.
- `inventory/declaration_spans.csv`: declaration-size triage, with line anchors.
- `inventory/imports.csv`: lexical import edges.
- `provenance/source_manifest.json`: complete selected-source authentication record.
- `provenance/verify_sources.py`: offline snapshot verification.
- `provenance/materialize_manifest.py`: reproduce snapshot from pinned public source URLs.
- `sources/Computability/DiophantineConsistency/tools/generate_*.py`: relevant source generators.
- Root config citations: [Lean toolchain](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/lean-toolchain), [Lake manifest](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/lake-manifest.json), [Lake targets](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/lakefile.toml).

## Umbrella import coverage (static only)

The lexical transitive local import closure of `DiophantineConsistency.lean` reaches 324 implementation-named files plus the umbrella. `OnePageDisplay54.lean` is the sole implementation-named file outside that closure; none of the 38 named Checks/Audit modules is reached. See `umbrella_closure.json`. This is not a claim about Lake library glob behavior or externally executed check scripts.
