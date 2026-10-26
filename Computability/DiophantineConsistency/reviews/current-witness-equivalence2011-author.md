# Direct current witness equivalence: author receipt

Date: 2026-10-26. Author: `/root/controller_certificate`. This is author
validation, not independent review. The author also implemented several native
word, carry, scalar, controller and Pell-front prerequisites. Root authored
the accepted `CurrentPositiveZero2011` composition reused here. Existing
machine calibration is imported unchanged.

## Frozen source and fresh checks

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `CurrentWitnessEquivalence2011.lean` | 65 | `2da5f02765c0c6a2856b8bd6e324cbd1fba3a98bd9d011b5e73190ebbb493758` |
| `CurrentWitnessEquivalence2011Checks.lean` | 51 | `fa60cb1d1e6979092177eccb1b6ce9e45f5ca4b6dc7315547911c6a0584ac6b7` |

The full sources and the directly reused endpoint/packing/Pell interfaces were
read before execution. Both new files passed their first fresh direct build:

```bash
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentWitnessEquivalence2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWitnessEquivalence2011.lean
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentWitnessEquivalence2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWitnessEquivalence2011Checks.lean
```

The main log `/tmp/current-witness-equivalence2011-main.log` is empty. The
focused log `/tmp/current-witness-equivalence2011-checks.log` has five intended
axiom reports, each exactly `propext`, `Classical.choice`, `Quot.sound`.
There were no source corrections, cap increases, dependency rebuilds, new
axioms, `sorry`, or native evaluation proofs. Only these new modules were
freshly compiled; no entire dependency-closure replay is claimed.

The resulting object hashes are respectively
`44992b61d87c407fc5c0b1c20df58c91a86d164c3c02665a5f3a3d14dc26e40f`
and `f14d7555d80733ed0d5a9ff082f7eb825717227ba820f997bf856332c19a6cde`.

## Exact scope

`blank_halts_positive_zero` consumes an explicit actual blank halt, calls the
existing `blank_halts_constructs_packing`, and assembles the same `packingData`
and population/Pell construction used by the accepted equivalence. It does
not call either `not_conZFC_constructs_packing` or `not_conZFC_positive_zero`.

`zfc_refutation_positive_zero` supplies that halt through the actual
`DecimalMachineZFC.blank_halts_iff_zfc_refutation` theorem. The converse opens
the actual positive tuple and uses `CurrentSoundness2011` without a consistency
premise. The exact result is `PositiveZero polynomial ↔ BProv ZFCax_s [] Form.fBot`.
The final `no_positive_zero_iff_conZFC` is obtained by applying these two maps
under negation. Its proof has no excluded-middle or double-negation-elimination
step. The focused checks also instantiate the literal `Carrier65.value` at
the entire fixed current port tuple in both directions and check the
pointwise no-solution formulation.

This is an external Lean equivalence. It does not claim that all imported
proofs are constructive, nor that HA or PA proves the sentence. The imported
K215 calibration still passes through the semantic lower 222-calculus and
constructible Choice arguments. Existing separate internal-arithmetic
validator/Rotation240 results may offer a reusable route, but their exact
connection to the current215 table and to the current equation remains a
distinct proof obligation. The source-level audit is in
`research/ha-current-equation-constructive-audit-20261026.md`.

No accepted source, shared status document, maintained equation, fixed port,
or Git state was changed by this packet.
