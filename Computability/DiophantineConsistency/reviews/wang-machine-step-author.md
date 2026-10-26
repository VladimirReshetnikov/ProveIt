# Actual machine-step color formula: author receipt

Date: 2026-10-26. This is an author receipt. Both complete new sources were read before their final bounded replay. Existing sources remain unchanged.

| Source under `Lean/DiophantineConsistency/` | Lines | SHA-256 |
| --- | ---: | --- |
| `WangMachineStep.lean` | 125 | `479ef25344a09804f3eeb6bd980e947941af55965ac48291349f90de14c3f100` |
| `WangMachineStepChecks.lean` | 87 | `7857b6376beb1fa12c47f4f4cb8f550edb666394d2f524e772a92d1e0fc73cf6` |

The main imports only frozen `WangMachineEncoding` (`0cb7f88e2cbc8fce77aed656a508d1154cb31c96d3ca2764c970591fc050806e`), whose transitive imports provide the actual BusyBeaver core. The checks import only the main. Both use `Elab.async false` and `maxRecDepth 10000`.

For arbitrary `M : Machine 215`, configuration `cfg`, and actual live state `cfg.state = some q`, `step_eq` gives the exact configuration record returned by `Machine.step`. Movement is left or right by exactly one, hence the new head differs from the old one. `read_written_at_moved` and `step_read_at_new_head` use `Tape.read_write_of_ne` to identify the destination bit with its value on the original tape.

`color_step` gives the entire color function after the step. At the new head it is `headColor a.next (Tape.read cfg.tape x)`; at the old head it is the written bit; elsewhere it is the original `color cfg x`. The theorem does not assume the action remains in an operating state. Separate new-head, old-head, elsewhere, and entering-halt corollaries preserve the actual optional next state, written tape and moved position. Entry into halt produces 432 or 433 according to the original destination bit.

The argument separates the distinct new-head and old-head cases before applying the existing read/write lemmas. It assumes neither tile-row semantics nor a run/tiling calibration. The synthetic checks cover leftward erasure, rightward writing into halt, both destination bits, unchanged remote cells, and negative controls excluding preservation of the old head color or assigning the halt head color to the old position.

Final commands from the repository root:

```text
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/WangMachineStep.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangMachineStep.lean
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/WangMachineStepChecks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangMachineStepChecks.lean
```

Both exited 0. Main log `/tmp/wang-machine-step-main-stage2.log` is empty, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`. Check log `/tmp/wang-machine-step-checks-stage1.log` has SHA-256 `dd4c0be9a5c9d34086bc52f25167c00b6ea2e69be5ae69f4ef524b4c33f7cc3f`; all 13 axiom reports contain only `propext` and `Quot.sound`, with the movement disjunction axiom-free. No final warnings, `sorry`, `admit`, `native_decide`, new axiom or target-equivalence premise occur.

The first main attempt had a multiline record indentation/parser error and an overly narrow simplifier that left `if True` unclosed. The final source fixes the record layout and simplifier without weakening any proposition. Its failed log remains `/tmp/wang-machine-step-main-stage1.log`.
