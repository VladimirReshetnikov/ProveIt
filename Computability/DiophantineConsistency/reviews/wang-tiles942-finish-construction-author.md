# Explicit halted, finish, initializer, and reset rows: author receipt

Status: **fresh Lean PASS**, 2026-10-26. Author: circuit-reduction agent. This is an author self-review/build receipt, not an independent peer review. I read the underlying actual initialization and finite constructor interfaces, the complete new 164-line module, and all 107 lines of focused checks before the fresh bounded builds. No frozen source or prerequisite object was changed.

## Frozen binding

Paths are relative to `Computability/DiophantineConsistency/` unless otherwise indicated.

| File | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/WangTiles942FinishConstruction.lean` | `b59a1698fdad679feb55bd6bb7a9eb440f46181204662f7245646522e403343d` |
| `Lean/DiophantineConsistency/WangTiles942FinishConstructionChecks.lean` | `3c5a2de8e5bd3ff80c7c16e1b08728e8d94e8bb4577d9578d09244359d273c4e` |
| Repository `.lake/build/lib/lean/DiophantineConsistency/WangTiles942FinishConstruction.olean` | `c405c2f0d1ab46e86ccfd22d653b4a8136274f3cf27fa3d9f567056b5b14f377` |
| `Lean/DiophantineConsistency/WangMachineEncoding.lean` | `0cb7f88e2cbc8fce77aed656a508d1154cb31c96d3ca2764c970591fc050806e` |
| `Lean/DiophantineConsistency/WangTiles942Language.lean` | `a28056b4929cfea69255619b5d89b5f7a64dc47efe0e94ca2e43e00f7788228d` |
| `/tmp/wang-finish-construction-main.log` | `93e69f9bb59565c002611d9488d34ddbbd5b486e9247082e9ac7ca73c13874f8` |
| `/tmp/wang-finish-construction-checks.log` | `6601a16670b56ad5313cad4ccb4ea58231cde25a0ce70a8772393cde76d4d4a9` |

Main imports exactly `WangMachineEncoding` and `WangTiles942Language`. Checks additionally import `WangTiles942InputLanguage` for a negative operating-head test.

## Literal definitions and proved interfaces

The namespace is `DiophantineConsistency.WangTiles942FinishConstruction`.

- `passTile cfg x = (0, color cfg x, 0, color cfg x)` and `finishTile cfg x = (0, color cfg x, 0, 438)`. Under the sole premise `cfg.state = none`, `passTile_allowed` and `finishTile_allowed` prove actual Allowed membership everywhere. At the head the proof uses the actual pass/finish constructor with first parameter 1, giving north 432 or 433. Away from the head it uses parameter 0 and the old tape bit. No tape normalization or support bound is assumed.
- Their complete color tuples and horizontal matching are proved directly. `pass_finish_matching` provides both repeated-pass and pass-to-finish vertical interfaces.
- `initialTile x` is exactly left initialization `(2,434,2,0)` for negative x, Start `(2,435,3,1)` at 0, head initialization `(3,436,4,4)` at 1, and right initialization `(4,436,4,0)` for x>1. All coordinates are integers. Each branch has its own lookup theorem and Allowed membership.
- `initialTile_north_mem` proves that its north color lies in the actual reset target list `[434,435,436]`. `initialTile_south` gives the exact encoded color of `DecimalMachineInitialization.initialized`, the actual state after the first blank-machine step. In particular the origin leaves symbol 1 and position 1 leaves head color 4; this is not an all-blank pre-step row.
- `initialTile_horizontal` covers all integers by the five cases x<−1, x=−1, x=0, x=1, and x>1. It proves the required orientation `west(x+1)=east(x)`, including all three changes at the distinguished coordinates.
- `resetTile x = (1,438,1,(initialTile x).north)` is Allowed by the actual reset constructor. Its colors, constant horizontal matching, finish-to-reset matching, and reset-to-initial matching are all explicit.
- `closing_rows cfg hh` bundles membership, exact initializer south, and horizontal matching for all four whole-integer rows. Complete vertical color and joining equalities remain separately available in the preceding API.

These are local whole-integer construction results. They do not select walls, prove a finite periodic/helical rectangle, choose a finite trace length, or assert machine/tiling or consistency equivalence. The halted-state premise is used only where required for actual pass/finish membership; unconditional tuple-equality lemmas do not purport to show membership without it.

## Focused checks

The checks cover halted-head colors 432 and 433, a negative head and duplicate-containing tape `[-3,-3,8]`, and plain written/blank cells away from the head. They verify that the pass row agrees with the actual stationary `Machine.step` of a halted configuration. A negative test proves that the pass tuple at the blank initial **operating** head is not Allowed: the exact north-input grammar forces its real transition with east rail 7, contradicting the proposed east 0. Thus the halted-state premise is not silently dropped.

Signed initializer positions −100, 0, 1, and 100 are checked, along with all three boundary edges and the actual south color 4 rather than the old 188. Reset outputs 434, 435, and 436 and the full finish/reset/initializer interfaces are tested. Each constructed tile is also shown to have an actual `Fin 942` table witness using the previously established exact Allowed/table equivalence.

## Fresh bounded builds

```sh
lake env lean -M6000 -j1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942FinishConstruction.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942FinishConstruction.lean
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942FinishConstructionChecks.lean
```

Both commands exited 0 on their first fresh compilation. Main: 3.81 seconds, peak 3,200,692 KiB, no Lean diagnostics. Checks: 3.75 seconds, peak 3,181,752 KiB, only twenty intended axiom reports. All reports use subsets of `propext`, `Classical.choice`, and `Quot.sound`; `resetTile_colors` and `resetTile_horizontal` use no axioms. No `sorryAx`, added axiom, or native-decision axiom occurs. Existing prerequisite objects were reused; no fresh replay of their full closure is claimed.
