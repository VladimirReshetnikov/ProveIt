# Actual run rows and variable-height trace cycle: author receipt

Status: **fresh Lean PASS**, 2026-10-26. Author: circuit-reduction agent. This is an author self-review/build receipt, not an independent peer review. I read the complete new 182-line module and 101-line checks before the final bounded builds. Frozen predecessor files were not edited.

## Frozen binding

Paths are relative to `Computability/DiophantineConsistency/` unless otherwise indicated.

| File | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/WangTiles942TraceCycle.lean` | `58ca5b2877426faf6704700f970043526c50873f429e9248552d8bb3019ca17e` |
| `Lean/DiophantineConsistency/WangTiles942TraceCycleChecks.lean` | `9934b7b6c05a83704474b842e2f425068ccadd05341b6c86dda0b453662d1081` |
| Repository `.lake/build/lib/lean/DiophantineConsistency/WangTiles942TraceCycle.olean` | `e70c5747e8de28b4ab833c21eee2026f1995f6eea67623813b404156cebe246a` |
| `/tmp/wang-trace-cycle-main.log` | `2a1cba10fb7bf9acc894f07320516c34ca1f69a7978703c47a507c94c2b5b6e8` |
| `/tmp/wang-trace-cycle-checks.log` | `0c10dd0085342ecf9a49aa3bd441e3a69c320c81a6cef92615cd0c5f588e775d` |

Exact main imports: `WangTiles942StepConstruction`, `WangTiles942FinishConstruction`, and `WangMachineTraceBounds`. Checks also import `WangTiles942InputLanguage` for a negative finish-membership test. These predecessors retain their separately frozen source hashes and author/peer receipts.

## Exact construction and premises

Namespace: `DiophantineConsistency.WangTiles942TraceCycle`.

`runTile t x` dispatches on the **actual** state of `DecimalMachine215.machine.run t`. A live state uses the proven step construction with that state; `none` uses the halted pass construction. The module proves unconditional Allowed membership and horizontal matching, north equal to the actual configuration's color at time t, and south equal to its color at time t+1. The halted south case uses the actual stationary step. `runTile_after_halt` shows that extra time is filled by the same literal pass row after a supplied actual halt time.

For `k : Fin H`, `cycleTile k x` is exactly:

1. `initialTile x` at k=0;
2. `resetTile x` at k+1=H;
3. `finishTile (machine.run k) x` at k+2=H;
4. `runTile k x` otherwise.

The branch order and the separate zero/last/finish/run lookup lemmas are explicit. `nextIndex hH k` is the finite index with value `(k.val+1)%H`; its interior successor and final wrap-to-zero values are proved directly.

`cycleTile_allowed T H hh hTH` uses only the actual halt hypothesis `(machine.run T).state = none` and `T+2≤H`. In the finish branch, k=H−2 implies T≤k, and the existing actual stationary-halt theorem supplies the required halted-state premise. All other membership branches come from the preceding constructions.

North and south color formulas retain the initializer separately. The initializer's output is color at actual run time **1**, established by the existing first-step theorem. The finish input remains color at its actual time H−2; the reset output is exactly the initializer's input. `cycleTile_temporal` proves north at `nextIndex k` equals south at k for every signed x, under `3≤H`. The proof separately handles initializer, last/reset, finish, and ordinary rows; reset→initializer is an explicit modulo-wrap case. This color equality does not itself need a halt premise; the premise is needed for Allowed finish membership.

`trace_cycle T H hh hTH hH` bundles actual Allowed membership, horizontal matching, cyclic temporal matching, and Start at row 0/position 0. It is valid at **every** height satisfying `T+2≤H` and `3≤H`. There is no width parameter or width/height divisibility condition. It does not establish that the actual machine halts; the halt time is a conditional input. It constructs a cycle of whole-integer rows, not spatial walls, a periodic/helical plane, a finite tile-word quotient, or a complete native/consistency equivalence.

## Checks and negative controls

The checks verify actual first-row output symbols 1 and 4, generic actual run-row semantics, stationary extra pass rows, finite successor/wrap values, exact H=3 and H=5 branch placement, and arbitrary extra height `H=T+3+extra` without a width premise. Reset wraparound is checked for every signed spatial position.

Two controls distinguish necessary premises. At height 2 the initializer/reset vertical edge mismatches, so the lower height condition cannot be simply dropped from the color statement. At height 3, the finish row at actual run time 1 is **not Allowed** at its operating head: exact input grammar would force its transition, whose south bit is at most 1, rather than 438. Thus color matching alone is not mislabeled as valid finite-language membership or as evidence of halting.

## Fresh bounded replay

```sh
lake env lean -M6000 -j1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942TraceCycle.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942TraceCycle.lean
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942TraceCycleChecks.lean
```

Both final commands exited 0. Main: 4.81 seconds, peak 3,201,608 KiB, no Lean diagnostics. Checks: 3.41 seconds, peak 3,178,560 KiB, only seventeen intended axiom reports. All reports use subsets of `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, new axiom, or native-decision axiom occurs. Existing dependency objects were reused; this is not a fresh replay of their full closure. Development fixes were explicit natural-one simplification, removal of unused arithmetic simplifications, and exposing a finite-index value before the existing run-one rewrite; no theorem premises were weakened or replaced by assumptions.
