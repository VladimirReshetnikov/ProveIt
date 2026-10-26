# Generic actual-machine trace bounds: author receipt

Status: **fresh Lean PASS**, 2026-10-26. Author: circuit-reduction agent. This is an author self-review and compilation receipt, not an independent peer review. I read the operational Core definitions and reusable lemmas, the complete new 142-line module, and all 85 lines of focused checks before their final bounded compilations. No frozen source or prerequisite object was changed.

## Frozen binding

Paths are relative to `Computability/DiophantineConsistency/` unless otherwise indicated.

| File | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/WangMachineTraceBounds.lean` | `2a4c16552c74a33445f8aa5302d5ab108f327708a08f468c4e61e6afcd85e718` |
| `Lean/DiophantineConsistency/WangMachineTraceBoundsChecks.lean` | `22e106989ecf6d9958fc6b86c650797d489b4b2734ca076391c8b2dedcae944c` |
| Repository `.lake/build/lib/lean/DiophantineConsistency/WangMachineTraceBounds.olean` | `7314d6ac41954c4276bab11a207b741e01b3745af4c2bcfe50496a5822bc6350` |
| Repository `Computability/BusyBeaver/Lean/BusyBeaver/Core.lean` | `436336133fa107c62eb00322333ec9451a0705964bd2b62fce3f44ce848672a6` |
| `/tmp/wang-trace-bounds-main.log` | `24ddcd91135cd091509e48229431420f7ec18ce2c1630e6513e73c54ab9eb66e` |
| `/tmp/wang-trace-bounds-checks.log` | `065926c1e837b5091aa6ea14ea79348f6783073caa2356f58a5eba8cd53582e8` |

Exact imports are `BusyBeaver.Core`, `Mathlib.Algebra.Order.Ring.Int`, and `Mathlib.Algebra.Order.Group.Abs`. The new proof is generic in the number of states and transition table, including zero-state machines. It imports no tiling calibration or old-layout module.

## Proved statements and dependency order

The namespace is `DiophantineConsistency.WangMachineTraceBounds`.

1. `step_head_bounds` proves that a single actual `Machine.step` changes the head by at most one. Its proof separately handles a halted configuration, which is unchanged, and an operating configuration, whose action's `Move` is left or right. It does not assume the action's next state is operating.
2. `step_read_of_ne` proves that any tape read away from the old head is unchanged by a step, using the actual `Tape.read_write_of_ne`. This includes write/move actions entering halt.
3. `runFrom_head_bounds` gives `initialHead − t ≤ currentHead ≤ initialHead + t` for every arbitrary initial `Config n`.
4. `runFrom_read_outside` proves that the tape read at x equals its initial read whenever `x ≤ initialHead − t` or `initialHead + t ≤ x`. The boundary is inclusive: the final write occurs before the final move, so it cannot yet have touched either extreme endpoint. The induction first uses the head bound at time t to show the time-(t+1) endpoint differs from the old head, then applies the unchanged-read step lemma and the previous-time invariant. No tape support or `Nodup` premise is present.
5. `run_eq_runFrom_initial` binds these results to Core's actual blank `Machine.run`, via its existing addition theorem. `run_head_bounds` and `run_head_abs_le` give the closed head interval `[-t,t]`. `run_read_outside` and `run_read_of_abs_ge` give the sharp uniform blank-tape bound `|x| ≥ t → read = false`, including every x at t=0.
6. `finite_trace_box M T L R` permits arbitrary independent natural margins `T < L` and `T < R`. For every t≤T, the head is strictly between integer walls −L and R, and every position on or beyond either wall reads false. There is no halting premise.
7. `finite_trace_margins` specializes to the explicit walls `−(T+1)` and `T+1`. Their distance is `2T+2`, with `2T+1` integer positions strictly between them. This is an operational trace bound, not a completed Wang-rectangle construction.
8. `run_eq_of_halted` reuses Core's stationary halted-run theorem. `halted_trace_box` therefore keeps the same arbitrary independent margins for every natural time once the explicit hypothesis `(M.run T).state = none` is given. It does not assert that an arbitrary machine halts.

The proofs require no normalized tape representation, unique-head premise beyond the actual Config record, tiling/run equivalence, or assumed finite support bound. They do not construct a periodic tile rectangle or establish cofinal tiling sizes; they supply the operational bounds for that later construction.

## Focused checks

A one-state machine that writes true, moves, and enters halt is checked in both directions. At time 1 the head reaches exactly +1 or −1, the old origin is true, and the new head reads false. Its later configurations are proved stationary. The same example shows that one cannot replace the uniform tape threshold t by t−1.

An arbitrary machine is run from an initial tape `[100,100]`, with head 7; at time 10 position 100 still reads true. This explicitly exercises an unnormalized tape and checks unchanged reads rather than incorrectly assuming blankness. Further checks cover an already-halted zero-state machine, the t=0 origin, independently unequal margins T+2 and T+9, and arbitrarily late times after a given halt time.

## Fresh bounded compilation

```sh
lake env lean -M6000 -j1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangMachineTraceBounds.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangMachineTraceBounds.lean
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangMachineTraceBoundsChecks.lean
```

Both final commands exited 0. Main: 2.47 seconds, peak 1,492,564 KiB. Checks: 2.24 seconds, peak 1,484,188 KiB. The main emitted no Lean diagnostics. All thirteen intended axiom reports use only subsets of `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, new axiom, or native-decision axiom appears. Existing imported object files were reused; no fresh replay of their full closure is claimed. An initial development compile exposed insufficient algebra/absolute-value imports; the final exact imports above resolved this without changing the theorem statements.
