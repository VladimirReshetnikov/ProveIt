# Compose shared coefficient entries with the exact controller-flow rewrite

The complete actual-table array costs **1,622=791M+831A operations**, with **146 positive witnesses**, twenty outer residuals and exact degree **35,587**. It combines the frozen [entry-shared1624 source](matrix193_entry_shared_coefficient_scout.md) with the independently proved [two-addition flow saving](matrix193_controller_flow_scout.md). The complete polynomial agrees with the1624 parent on every supplied tuple, so its ordinary-input language and positive zero set are unchanged. The established universal84 bound is unchanged.

## Exact composition

The [new standalone helper](matrix193_entry_flow_scout.py) reads both frozen parent trios as inert bytes/JSON, imports or executes none of their programs, and emits the actual complete source in the [receipt](matrix193_entry_flow_scout.json). The six pins are:

| Dependency | SHA-256 |
|---|---|
| Entry-shared Python | `e5223ccc69d6c42fff7b5fadfae29fa1d9039d513967f27ed0cb48a8e9fb4bee` |
| Entry-shared JSON | `a59d1a571695a028d96947d4e2ccd0566af763b272dc170a11d7d1fb92c1c04c` |
| Entry-shared proof | `80bdcde5242044365bdcc904d42964c8d083b3a41e894694e438b60da6b51f70` |
| Flow Python | `9d9a2dbd121d73a1aee8a34c462db203d9cfd47c42d8302bddf2e602e1dfc49b` |
| Flow JSON | `766d4a77c9c7cfe97dd1131e8c9df9dfa62892206d82fc2d609b9e10b838793e` |
| Flow proof | `dcc21d29f0bad6f8c07cb3bb5a88831bd127c01f9b6ac4ffd4169265b275269f` |

Start from every row of the actual1624 array. Its flow cone still uses the paid values bm=B−1, P=bm*J+1 and raw LOAD/SWITCH words EL,ES. The exact removed rows are:

    r2321=J−EL;
    r2322=r2321−ES;
    r2323=r2322+P;
    r2324=B*r2321.

Replace them with:

    flow_scaled_load=bm*EL;
    flow_switch_position=flow_scaled_load+1.

The existing residual r2364 changes from r2323−r2324 to flow_switch_position−ES. Its subtraction, square and all finalizer joins stay paid. The new helper reconstructs the four old definitions and their actual paid bm/P dependencies; it checks that these are precisely the frozen flow edit and that their sole outside consumer is r2364. It verifies that all578 entry-shared coefficient rows remain literal and live. Thus the two optimizations do not require any new coefficient assumption or witness coordinate.

A fresh exact expansion in formal B,J,EL,ES proves

    (J−EL−ES)+((B−1)J+1)−B(J−EL)
      =1+(B−1)EL−ES.

This uses no zero equation, controller typing, positivity or division. Substituting the actual paid definitions therefore preserves the residual over every commutative ring. Every other retained producer is literal. Using only this proved residual as a common formal atom, full expression interning verifies all1,620 retained parent rows, all six native inputs, all twenty residuals and the final output. Hence

    F_1622=F_1624

on identical ordinary input, fixed coefficient ports and supplied witnesses. No positive witness reconstruction is required, and no extraction coordinate is reinterpreted.

## Full count, degree and domain

The new array has unique producer names, valid topological order, and complete output liveness for every paid row and every supplied port. The count comes from the emitted rows:

| Packing | Native | Outer producers | Finalizer | M | A | Total | Witnesses |
|---:|---:|---:|---:|---:|---:|---:|---:|
|830|63|667|62|791|831|1,622|146|

Four producers costing1M+3A are removed and two costing1M+1A are inserted. There are137 distinct integer literals, separate from the unchanged eight fixed coefficient ports. All63 native rows remain literal, and the62-row finalizer differs only in the two operands of its already paid flow residual.

Exact degree35,587 transfers directly through the complete identity on every valid fixed-program specialization. In particular the bounded-high parent's nonzero SWITCH term in the tied leading extraction bracket is unchanged. The independently recomputed syntactic upper bound36,547 is not asserted to be the exact degree. No dense expansion of the full polynomial is needed for this degree transfer.

The fixed99-edge controller,340 selected-coordinate lanes, matrix table, bounded-high chart, native kernel and ordinary-input bridge retain their inherited interpretation. Arbitrary fixed-port assignments satisfy the arithmetic identity; the simulation theorem still requires the valid fixed-program recipe. This is an improvement to the alternate matrix route, not a new universal minimum.

## Fresh evidence and replay

Thirty-two fresh complete-source comparisons over two prime fields check every common register and final output; half use the saved illustrative fixed coefficients and half vary all supplied ports, including signed values. These are supplemental arithmetic diagnostics, not compiler histories. The exact residual and full source identity are the proof.

Only the actual-table source is emitted here. The receipt identifies the diagnostic301=126M+175A/51-witness array by its hash and ledger from the pinned flow parent; it explicitly marks that source as neither emitted nor replayed in this packet. No diagnostic saving is attributed to the entry-pair structure. No giant outer fixture or native Pell tuple is newly materialized.

The parser rejects duplicate keys and nonfinite JSON. Explicit exception checks and canonical type-sensitive receipt comparison remain active under `-O`. The receipt stores the new helper's source hash and all six dependency hashes. After installation:

```sh
entry_flow_wip=/absolute/path/to/native-stream-queue
python3 "$entry_flow_wip/matrix193_entry_flow_scout.py" \
  --root "$entry_flow_wip" --expect "$entry_flow_wip/matrix193_entry_flow_scout.json"
python3 -O "$entry_flow_wip/matrix193_entry_flow_scout.py" \
  --root "$entry_flow_wip" --expect "$entry_flow_wip/matrix193_entry_flow_scout.json"
```

Use `--output FILE` to regenerate. Fresh generation and fresh normal and optimized exact receipt replays from `/` passed with the six parents under the explicit staging root `/tmp`. No frozen predecessor or repository file was changed.
