# Literal machine configuration colors: author receipt

Date: 2026-10-26. This is the implementation author's receipt. Both complete new sources were read before their final bounded compilation; no existing source was edited.

## Frozen sources

Both files are in `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `WangMachineEncoding.lean` | 171 | `0cb7f88e2cbc8fce77aed656a508d1154cb31c96d3ca2764c970591fc050806e` |
| `WangMachineEncodingChecks.lean` | 91 | `eb23dd938d3e890fa6578f50911266ff15e8fd6fd975e70b527bb38b7397ed23` |

The main imports only `DiophantineConsistency.DecimalMachineInitialization`, frozen SHA-256 `748587f903a4a1cc0d0c475ebc0ba9628887eaff0584e6d3a7944f4115b6b82f`. The checks import only the new main. The initializer packet's provenance and exact source bindings are recorded in [its author receipt](decimal-machine-initialization-author.md). Both modules disable asynchronous elaboration and set `maxRecDepth` to 10000.

## Scope and proof

`stateNumber` sends operating `some q` to the actual `Fin 215` value and sends `none` to the table's halt-state number 215. Its value is bounded by 215 and it is injective. `headColor` applies the literal `WangTiles942.headColor` constructor to this state number and the Boolean tape bit. It is between 2 and 433; equality recovers both the state and bit. The proof uses the one-bit bound and the mixed-radix expression `2*q+b+2`, not any table or machine-calibration premise.

`color cfg x` reads the actual finite-support tape. At the configuration's head it emits the corresponding head color; elsewhere it emits the plain bit. The module proves plain colors at most 1, all colors at most 433, and `2 ≤ color cfg x ↔ x = cfg.head`. It does not identify different tape-list representations as different row meanings, nor require tape lists to be normalized.

`step_enter_halt` unfolds the actual generic `Machine.step`: an action with next state `none` still writes its bit at the old head and applies its left/right movement. `step_enter_halt_color` encodes the resulting moved head as 432 plus the bit read from that written tape at the moved position. Thus halting does not erase the write, retain the old head, or replace the configuration before movement. Focused synthetic transitions exercise both halted colors 432 and 433 and distinguish the old plain cell from the moved head.

For the actual decimal machine's proven post-first-step configuration, `initialized_color` gives exactly `if x = 0 then 1 else if x = 1 then 4 else 0` for every integer position. The focused checks transport this formula to the actual `machine.run 1` using the frozen initializer theorem. The decimal numeral is not reevaluated.

This packet supplies literal vertical-color semantics for a configuration. It assumes no tiling, decoded machine run, reset/finish interpretation, or consistency equivalence, and proves no complete tiling/run correspondence.

## Fresh bounded verification

The final commands, from the repository root, were:

```text
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/WangMachineEncoding.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangMachineEncoding.lean
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/WangMachineEncodingChecks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangMachineEncodingChecks.lean
```

Both exited 0. `/tmp/wang-machine-encoding-main-stage2.log` is empty, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`. `/tmp/wang-machine-encoding-checks-stage1.log` has SHA-256 `afa8f6b4dd42cbd348e575d3019b64c4ac45326712afd81c5e75e795906772d6`. Its 18 reports contain only the standard `propext`, `Classical.choice`, and `Quot.sound`, with several arithmetic/definitional theorems axiom-free. Final logs contain no warnings. No `sorry`, `admit`, `native_decide`, new axiom, or target-equivalence premise was added.

The first main build stopped only at `color_at_head`, because an overly narrow `simp only` list left `if True` unsimplified. Replacing that tactic by `simp [color]` closed the same unchanged proposition; its earlier log remains `/tmp/wang-machine-encoding-main-stage1.log`. Every other initial main proof passed unchanged.
