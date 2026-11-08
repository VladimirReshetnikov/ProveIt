# iPRA endpoints for package 179's ten-positive 90/206 centred circuit

Package 179's `positive/late172/centerA_radix67.json` (mode `centerA`,
90 operations, exact degree 206, weight `L = bV`; proof:
`positive/late172/PROOF.md`) is package 172's 87/214 free-inverse circuit with
the transport gate `n - L B` replaced by `n - V (b B + g0)` at the centre
`g0 = A U E` (JSON rows `A = Am1 + 1`, `g0 = A · UE`, `bB`, `bB_g0`,
`LBt = V · bB_g0`; the Lean register `A` is `Am1 + 1`, package 179's `A`).
The `_start4177` copy is another tuple and is not covered.

The `coefficient_binding` equals the 75/402 graph's in every port field except
the relative `path` and an explicit `endianness: little` annotation, with the
direct-BFS943 raw hashes (K0 `0a86821a…`, MC `6007cabd…`, MF `48333b0d…`,
β `0664a868…`).

The Lean endpoints are in `Lean/DiophantineConsistency/BFS943/IPRATrace90.lean`
(namespace `DiophantineConsistency.IPRATrace90`): `positiveBridge`,
`native_equivalence`, `standard_equivalence`, `reference_equivalence`,
`standard_translated_equivalence`, `reference_translated_equivalence`, at the
same ports `fixedPorts` as `IPRATrace75`. Each depends only on `propext`,
`Classical.choice`, `Quot.sound`.

## Route

Exactly the route of `research/ten-positive-p179-89-endpoint` (the shared
`Trace87Shift*` and `Centred87*` layers are recorded there); only the centre
changes. `Trace90Regs`: `centre = A (U E)`,
`value90 = TenPositiveCentred87.valueAt p v (centre p v)`;
`Trace90Centre.gnat = (Am1 + 1) U E` and `gnat_bound` is
`4 E (1 + a) - g0² = 4 E + (U E)² (3 A² + 6 A - 1) > 0` (`A = Am1 ≥ 1`),
i.e. 179's `g0 < 2 g`. `Trace90ModelIff.positive_model_iff` is
`Centred87Sign.shift_zero` + `Trace87ShiftSource` + `FixedSourceHalt` for
soundness and `Trace87HaltGraph` + `Centred87Complete` for completeness.

## Binding check

`check_lean_graph.py` (run `py -I -X utf8 -B check_lean_graph.py`) is the 89
record's checker at this point: pins the 90 JSON, its parent 87 JSON, the 75
JSON, the 87 checker and the Lean sources it reads; checks the metadata and
that the rows differ from the 87 rows exactly by the centring gates (including
`A = Am1 + 1`); compares the transcribed `value90` with the JSON output after
exact commutative-ring structural normalization (also `g0`, `bB_g0`, `LBt`,
`Znum`, `Mtot`, `sixq7`, `eclear`); rejects five mutations (gate sign, the
uncentred 87 gate, gate weight `b` for `V`, the other centre `Am1 + 2`, centre
without `E`); checks the literal/endpoint definitions and `fixedPorts`.
Output: `check-output.json`. Finite external checks, not Lean theorems about
files.

## New modules (all in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `Trace90Regs` | `centre`, `value90`, `Trace90Centre.gnat`, `gnat_bound` |
| `Trace90Syntax` | literal `TenPositiveTrace90.expression`, `Trace90BFSSyntax.literal_zero_iff` |
| `Trace90ModelIff` | `positive_model_iff` |
| `IPRATrace90` | the iPRA endpoints |
