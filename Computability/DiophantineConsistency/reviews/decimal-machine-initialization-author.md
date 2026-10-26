# Exact decimal-machine initialization: author receipt

Date: 2026-10-26. This is the implementation author's receipt, not an independent peer review. Both new sources were read completely before their final bounded compilation. Existing decoder, table, machine, native, and arithmetic files were left unchanged.

## Frozen sources and imports

Paths below are relative to `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| Source | SHA-256 |
| --- | --- |
| `DecimalMachineInitialization.lean` | `748587f903a4a1cc0d0c475ebc0ba9628887eaff0584e6d3a7944f4115b6b82f` |
| `DecimalMachineInitializationChecks.lean` | `60cf20b9b63f90a53e03b9250130c57c9c5769a955b865d917baf941c63a5ee9` |

The main module imports only `DiophantineConsistency.WangTiles942Core`; the checks import only the new main module. Both disable asynchronous elaboration and set `maxRecDepth` to 10000.

Relevant unchanged source bindings:

| Source | SHA-256 |
| --- | --- |
| `WangTiles942Core.lean` | `7471a9ff93f06d0eb39c2f3791d5db28dd2927e6346213173f38c2b3ea150d85` |
| `WangTiles942Data.lean` | `ac9047c705dddbab3bec84265beff2d72d498496bde12261cc76c46dc0c5a125` |
| `DecimalMachine215.lean` | `da9e49c1a5f47a10d1f385810e1e89d2e3f4f25fc438dc85cf2184efdc3c719a` |
| `Computability/BusyBeaver/Lean/BusyBeaver/Core.lean` | `436336133fa107c62eb00322333ec9451a0705964bd2b62fce3f44ce848672a6` |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDense215.lean` | `b1ebe573ced4b336ead43dbe7278ad97c8d28c06412b43c7291d051b98c6395a` |

## Verified statement and reasoning

`first_action` transports the already kernel-proved cached first action `(true,true,1)` through `WangTiles942.action_eq_decoder`. It does not reevaluate the 715-digit numeral. `first_transition` then unfolds the actual `KDense215.act` convention and proves that the machine in state 0 reading blank writes `true`, moves right, and enters state 1.

The exact configuration `initialized` has state `some 1`, integer head position 1, and finite-support tape `[0]`. `step_initial` and `run_one` identify it with the actual machine's first step from `initial 215`. The tape theorems quantify over every integer position: it reads `true` exactly at zero, and `false` everywhere else, including at the current head. The checks explicitly include a negative position and prove this configuration differs from the blank initial configuration.

`runFrom_initialized t` is exactly the original run at time `t+1`, by the existing generic `Machine.run_add_eq_runFrom` theorem. `blank_halts_iff_initialized` proves equivalence of halting from the blank initial configuration and from this initialized configuration; it explicitly excludes a halt at blank time zero. This uses the same actual machine on both sides.

The table calibration is deliberately componentwise. Start's south color is 1; `headColor 1 0` is 4; the actual abstract initializer tile 928 has south color 4. The literal tail rows 927, 928, 929 are checked in the finite `tailRows` list, and rows 927 and 929 have south color 0. `initialization_components` identifies the Start and head colors with the actual post-step tape readings. These statements do not define or assume complete row semantics, spatial placement, or a general machine-run extraction theorem.

## Fresh verification

From the repository root, the final commands were:

```text
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/DecimalMachineInitialization.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/DecimalMachineInitialization.lean
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/DecimalMachineInitializationChecks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/DecimalMachineInitializationChecks.lean
```

Both exited 0. The final main log `/tmp/decimal-machine-initialization-main-stage2.log` is empty (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). The check log `/tmp/decimal-machine-initialization-checks-stage1.log` has SHA-256 `c30f3ed237c3ac1339566531093622af79700b1fb4e214c9eab4e72d8641bd9c`. Its 18 axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`, with the head-color arithmetic axiom-free. No warning remains in the final logs. No `sorry`, `admit`, `native_decide`, new axiom, or target-equivalence premise was added.

The first main build failed only in two finite-state elaborations: rewriting a constructor-form state zero by the numeral-form transition theorem, and closing an explicit `some ≠ none` goal. The final source supplies `Fin.ext` for the former and `Option.some_ne_none` for the latter. The earlier failed log remains `/tmp/decimal-machine-initialization-main-stage1.log`; no mathematical assertion was weakened.

This packet establishes the actual seeded configuration and the exact clock shift. It does not yet prove the correspondence between complete marked Wang tilings and machine runs, nor the final equation/consistency equivalence.
