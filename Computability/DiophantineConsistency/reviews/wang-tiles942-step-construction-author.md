# Actual machine step to Wang row: author receipt

Status: **fresh Lean PASS**, 2026-10-26. Author: circuit-reduction agent. This is an author self-review/build receipt, not an independent peer review. I read the complete imported Action and Step interfaces and operational definitions, the full 159-line new module, and all 114 lines of focused checks before the final bounded compilations. No frozen source or prerequisite object was changed.

## Frozen source and replay binding

Paths are relative to `Computability/DiophantineConsistency/` unless otherwise indicated.

| File | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/WangTiles942StepConstruction.lean` | `935bfb4b2762bd099185350f3869114c81f11140a823951e6319a33ce292138f` |
| `Lean/DiophantineConsistency/WangTiles942StepConstructionChecks.lean` | `5e8c6382fceabcf880ca431af455cb71d90350b107c10f5c748eb3a4dd688a92` |
| Repository `.lake/build/lib/lean/DiophantineConsistency/WangTiles942StepConstruction.olean` | `3f45c3b95da12326c9b15fd930f2993fdb3cb722f1fbe90822273f2ecf987049` |
| `Lean/DiophantineConsistency/WangMachineAction.lean` | `1776d84d82ae32ec58287779e639ce163bf0e10dec24056effc3aa4c2f1d3bd5` |
| `Lean/DiophantineConsistency/WangMachineStep.lean` | `479ef25344a09804f3eeb6bd980e947941af55965ac48291349f90de14c3f100` |
| `/tmp/wang-step-construction-main.log` | `7877e5a0f81937ac3c8df8a099ff514b7524b29771e2d62000e485a7d3d0b4b6` |
| `/tmp/wang-step-construction-checks.log` | `12b8894ea61f925ad7b6df2bbd874df2d7ad1d810f9c1ca13d1d5ecbd76d46f1` |

The module imports exactly `WangMachineAction` and `WangMachineStep`. The actual finite-language and decoder/cache calibration arrive through those existing modules. No action table or decimal numeral is independently redefined or reevaluated here.

## Literal construction

In namespace `DiophantineConsistency.WangTiles942StepConstruction`, `sourceIndex cfg q` is the actual Action input index at the old head. `nextHead cfg q` uses the actual decimal machine transition's move. `receiveTile cfg q x` uses the cached action's direction and exact target, and the **old tape bit at x**. `stepTile cfg q x` is the transition tile at the old head, the receive tile at the moved head, and the plain pass tuple elsewhere.

`nextHead_ne` proves that the first two branches cannot overlap. `nextHead_eq` binds the destination to the cached direction and the exact integer displacement ±1. The old-head, new-head, and elsewhere lookup lemmas expose all three branches.

`receiveTile_allowed` uses `action_target_mem` for the action's own direction and does not restrict its target to an operating state. `stepTile_allowed` therefore gives membership in the actual finite table language at every integer x. It needs no state premise, since the construction is parametrized by q. Interpreting the row as the step of cfg requires precisely `cfg.state = some q`.

`stepTile_north` gives the actual configuration's encoded north color at every x. At the old head it uses the two arithmetic projections of the actual action index; elsewhere it is exactly the old tape bit. `stepTile_south` invokes the actual operational step equations at the old head, moved head, and every other position. The target-to-optional-state theorem converts the receive tile's target into the actual new head color, including target 215 and halt colors 432/433.

`stepTile_west` and `stepTile_east` give complete formulas for the only possible horizontal signal. For a right move it occupies the edge from old head to new head; for a left move it occupies the reverse-adjacent edge. `stepTile_horizontal` proves `(stepTile (x+1)).west = (stepTile x).east` for every integer x using the exact displacement identity. There is no finite-boundary or implicit right-direction assumption.

The public endpoint `step_row cfg q hq` bundles Allowed membership, exact north, exact south, and horizontal matching. Its only premise beyond the configuration and q is the literal live-state equality. It constructs the row; it assumes no row/step equivalence, run representation, tape normalization, target-not-halt condition, or uniqueness premise about an external tiling. This is one operating-step construction, not yet a finite periodic rectangle, halted-padding row, complete trace tiling, or consistency equivalence.

## Checks

The checks build an existential whole-integer row from only a live cfg, and recover an actual Fin 942 table witness for each constructed tile. They specialize the output at a moved head entering halt to `432 + old destination bit`.

Concrete checks use the authenticated small action cache and existing transition bindings:

- The first blank action produces transition `(0,2,7,1)` at 0 and receive `(7,0,0,4)` at 1.
- Actual action 125 is exercised at old head −5 with tape `[-5,-4,-4]`: its transition is `(0,127,204,1)`, its receive at −4 is `(204,1,0,433)`, and the actual machine step has state `none`. The repeated tape entry makes explicit that no normalized-tape premise is used, and destination bit one tests old-destination reading.
- Actual left action 5 produces `(0,1,205,11)` at the moved head.

The checks use only existing theorem-based binding to the decimal machine. An early development check exposed an unnecessary definitional reduction of a concrete decimal transition; the final check instead projects the existing generic `step_enter_halt` theorem and emits no exponentiation warning.

## Fresh bounded compilation

```sh
lake env lean -M6000 -j1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942StepConstruction.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942StepConstruction.lean
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942StepConstructionChecks.lean
```

Both final commands exited 0. Main: 3.93 seconds, peak 3,200,688 KiB. Checks: 3.78 seconds, peak 3,195,248 KiB. The main emitted no Lean diagnostics; the checks emitted only thirteen intended axiom reports. All reported dependencies are subsets of `propext`, `Classical.choice`, and `Quot.sound`; there is no new axiom, `sorryAx`, or native-decision axiom. Imported dependency objects were reused; no fresh replay of their full closure is claimed.
