# Literal action / actual machine bridge: author receipt

Date: 2026-10-26. Author receipt for two new, completely read sources. Existing frozen files were not changed.

| Source under `Lean/DiophantineConsistency/` | Lines | SHA-256 |
| --- | ---: | --- |
| `WangMachineAction.lean` | 119 | `1776d84d82ae32ec58287779e639ce163bf0e10dec24056effc3aa4c2f1d3bd5` |
| `WangMachineActionChecks.lean` | 98 | `f34414842cee2e898bd17712d5db800ca527d6408b1bb7be7328afac3bfe062c` |

The main imports `WangMachineEncoding` (SHA-256 `0cb7f88e2cbc8fce77aed656a508d1154cb31c96d3ca2764c970591fc050806e`) and `WangTiles942Language` (`a28056b4929cfea69255619b5d89b5f7a64dc47efe0e94ca2e43e00f7788228d`). Checks additionally import frozen `WangMachineStep` (`479ef25344a09804f3eeb6bd980e947941af55965ac48291349f90de14c3f100`) to verify composition. Both new modules use `Elab.async false` and `maxRecDepth 10000`.

## Exact binding

`inputIndex q b : Fin 430` has value `2*q.val+b.toNat`. Its quotient and remainder modulo 2 recover the state and read bit; its value plus 2 is exactly the literal transition tile's north head color.

`transition_eq_cached` uses the already proved all-action `WangTiles942.action_eq_decoder` equality and the actual definition of `DecimalMachine215.machine.transition`. It identifies the transition with `KDense215.act` applied to the cached action at this index. `transition_write`, `transition_move` and `transition_moved_head` expose the actual write bit and direction conventions without changing either decoder.

`action_target_lt` derives every cached target's bound `<216` from `WangTiles942Language.action_target_mem` and the frozen literal target-list bound. No new 430-entry closed calculation or decimal-numeral evaluation is used. For any target satisfying that bound, `act_stateNumber` proves that the optional next state recovers its numeric target: numbers below 215 are operating states, and 215 is exactly `none`. The corresponding `act_next_none_iff`, `transition_stateNumber` and `transition_next_none_iff` retain this distinction. The bound is indispensable; a focused negative control demonstrates that the raw operational convention would map invalid target 216 to halt as well.

`transition_headColor` identifies the encoding of the actual next state and an arbitrary destination read bit with the literal table's head constructor at the cached numeric target. This includes halted head colors 432/433. A focused theorem composes it with the generic operational step formula, retaining the original destination bit.

The checks kernel-reduce the actual cached target at input index 125 (state 62, read `true`) and then use the bridge to prove that the actual machine transition halts. This checks the early actual halt without reevaluating its decimal decode. The main results themselves remain uniform in all operating states and read bits.

No tiling, row, machine-run extraction, or consistency-equivalence premise is introduced. This is the literal action binding needed to identify independently derived tile-row output colors with the actual operational step.

## Fresh bounded replay

Final commands from the repository root:

```text
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/WangMachineAction.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangMachineAction.lean
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/WangMachineActionChecks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangMachineActionChecks.lean
```

Both exited 0. Final main log `/tmp/wang-machine-action-main-stage2.log` is empty, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`. Check log `/tmp/wang-machine-action-checks-stage1.log` has SHA-256 `a287d68c5a100db8f95962a0330bedbf2a74e786229239e2e9d1ebb4173d565d`; its 13 axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. No final warnings or new axioms, `sorry`, `admit`, `native_decide`, or target-equivalence assumptions occur.

The first main build already passed; it reported one unused simplifier argument in the target215 branch. That unused argument was removed, the change was read, and the final main replay was clean. Its earlier warning log remains `/tmp/wang-machine-action-main-stage1.log`.
