# iPRA endpoints for package 179's ten-positive 89/210 centred circuit

Package 179 (`con-zfc-diophantine-forms/179-affine-horizons-centered-certificates`)
supplies, in `positive/late172/`, two centred versions of package 172's
87/214 free-inverse circuit (proof: `positive/late172/PROOF.md`). This record
covers `centerAp1_radix67.json` (mode `centerAp1`, 89 operations, exact degree
210, weight `L = bV`) and the shared centred layer; the companion
`centerA_radix67.json` (90/206) is `research/ten-positive-p179-90-endpoint`.
Only the `_radix67` copies are on the direct-BFS943 tuple; the
`_start4177` copies are a different tuple and are not covered.

In the notation of `research/ten-positive-p172-87-endpoint` the circuit
replaces the 87 transport gate `n - L B` by `n - V (b B + g₊)` with
`g₊ = (A + 1) U E` (JSON rows `g0 = Ap1 · UE`, `bB`, `bB_g0`,
`LBt = V · bB_g0`; the Lean register `Am1` is `A - 1`, so `A + 1 = Am1 + 2`).
Everything else is the 87 circuit, so identically `Z = Z₈₇ - M (g₊ V)`.

The `coefficient_binding` equals the 75/402 graph's in every port field except
the relative `path` and an explicit `endianness: little` annotation (the 75
graph's integers are the little-endian ones): the direct-BFS943 tuple, K0 raw
`0a86821a…`, MC `6007cabd…`, MF `48333b0d…`, β `0664a868…`.

The Lean endpoints are in `Lean/DiophantineConsistency/BFS943/IPRATrace89.lean`
(namespace `DiophantineConsistency.IPRATrace89`): `positiveBridge`,
`native_equivalence`, `standard_equivalence`, `reference_equivalence`,
`standard_translated_equivalence`, `reference_translated_equivalence`, at the
same ports `fixedPorts` as `IPRATrace75`. Each depends only on `propext`,
`Classical.choice`, `Quot.sound`.

## Route

Package 179 §2 notes that the inverse shift `n ↦ n - ĝ V` need not preserve
positivity, so there is no zero-set transfer to 87. The Lean route instead
reuses the 87 analysis at a shifted carrier.

**Shifted 87 analysis** (`Trace87Shift*`, reusable for any carrier shift).
`Trace87ShiftTransport.ShiftZero p v ws` says: the 87 norm value vanishes at
the carrier `Z₈₇ - M ws`, and `B ≥ 0`. After `B ≥ 0` the 87 soundness proof
reads the carrier only modulo `D` and modulo `H`, and `M ws` is divisible by
both; the norm layer (`Trace87NormRoots` … `Trace87NormOffset`) is already
generic in the carrier. So `Trace87ShiftTransport`, `…Projection`,
`…VariableHeight`, `…GraphPower`, `…Unweighted`, `…Integral`, `…Sandwich`,
`…Source` are the 87 modules with the hypothesis `value87 = 0` replaced by
`ShiftZero p v ws` (mechanical copies; the only proof changes are the
divisibility witnesses in `graph_zero_data` and `graph_projection_divisibility`,
and `transport_divisor` at the signed index `n - ws` in `graph_source_parts`).
`Trace87ShiftSource.source_of_fixed_zero` gives
`BFS943FixedSource.FixedSource` at `Trace87Source.sourceVal`.

**Centred registers** (`Centred87Regs`, `Centred87Syntax`):
`TenPositiveCentred87.regsAt p v g` is the 87 register map with the centred
carrier at an arbitrary centre value `g`, `valueAt` its norm polynomial;
`Z_shift` (`Z = Z₈₇ - M (g V)`), `valueAt_norm`, and `valueAt_shift`
(updating `n` to `n + g V` turns `value87` into `valueAt`).

**Sign** (`Centred87Estimate`, `Centred87Sign`): package 179's (3)–(4).
`centred_estimate` is `Trace76Estimate.bv_estimate` with `16 g ≤ F` for
`8 g ≤ F` and a centre `0 ≤ ĝ < 2 g`: `F |b| ≥ V0 - c > 2B - c > F²/2 ≥ 8 g F`,
so `|b| > 8 g` and `2 (g y + ĝ |V|) < b V`. `Centred87Sign.sixteen_le` gives
`16 τ f ≤ 1 + 2a` from `D ≥ 16`, `U ≥ c² ≥ 4`. For a natural centre with
`ĝ² < 4 G` (`G = E F0 = (τ f)²`), `nonnegative` reads the centred carrier as
the 87 carrier with root `z + ĝ V` and applies
`TenPositiveCarrierTransport.model_nonnegative_of_carrier` (offset bound
`2 eclear < b V D` as in 87) at the positive `n` of the centred zero itself.
`shift_zero` packages `B ≥ 0` as `ShiftZero p v (ĝ V)`.

**The centre** (`Trace89Regs`): `centre = (Am1 + 2) (U E)`,
`value89 = valueAt p v (centre p v)`; `Trace89Centre.gnat` is its natural
representative and `gnat_bound` is
`4 E (1 + a) - g₊² = 4 E + (U E)² (3 A² + 4 A - 4) > 0` (`A = Am1 ≥ 1`).

**Completeness** (`Centred87Complete`): a halting time gives a positive 87
zero (`Trace87HaltGraph.halt_zero_of_model_ports`). `V_positive` reads
`V > 0` there from the 87 soundness layer (mask, `R = rank`,
`c = ψ_A(R) ≥ R`, so `b = c T - R ≥ 0`, and `b V > 2 τ f y > 0`), not from the
construction; `centred_zero` moves `n` to `n + ĝ V` (`Function.update`), so the
centred carrier equals the 87 carrier and the value is unchanged. The centre
does not read `n` (`gnat_update` is `rfl`).

`Trace89ModelIff.positive_model_iff` joins both directions; the iPRA wrappers
are those of `IPRATrace75`.

## Binding check

`check_lean_graph.py` (run `py -I -X utf8 -B check_lean_graph.py`) pins the
89 JSON, its parent 87 JSON (also checking the JSON's `parent.sha256`), the 75
JSON (port binding), the 87 record's checker (whose parser and normalizer it
imports) and the Lean sources that checker reads (`TenPositiveTrace75.lean`,
`Trace79Regs.lean`, `Trace82Regs.lean`, `Trace87Regs.lean`). It checks the
graph metadata and that the JSON rows differ from the 87 rows exactly by the
centring gates; transcribes `value87` with the 87 checker (and re-checks it
against the 87 JSON), then parses `regsAt`, `valueAt`, `centre` and `value89`
into the same interned DAG and compares with the JSON output after exact
commutative-ring structural normalization (also the rows `g0`, `bB_g0`,
`LBt`, `Znum`, `Mtot`, `sixq7`, `eclear`). It rejects five mutations (gate
sign `- g`, the uncentred 87 gate, gate weight `b` for `V`, the other centre
`Am1 + 1`, centre without `E`), checks the literal and endpoint definitions
verbatim and that `fixedPorts` is textually the `IPRATrace75` one, so
`reviews/bfs943-source-promotion/tools/check_ports.py` covers this circuit.
Output: `check-output.json`. These are finite external checks, not Lean
theorems about files.

## New modules (all in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `Trace87ShiftTransport` | `ShiftZero`; carrier data at the shifted carrier |
| `Trace87ShiftProjection` … `Trace87ShiftSandwich` | the 87 chain under `ShiftZero` |
| `Trace87ShiftSource` | shifted 87 zero ⇒ `FixedSource` |
| `Centred87Regs` | `regsAt`, `valueAt`, `Z_shift`, `valueAt_shift` |
| `Centred87Syntax` | `evalRing_valueAt` |
| `Centred87Estimate` | `centred_estimate` (ordered rings) |
| `Centred87Sign` | `sixteen_le`, `graph_centred_bound`, `nonnegative`, `shift_zero` |
| `Centred87Complete` | `V_positive`, `centred_zero` |
| `Trace89Regs` | `centre`, `value89`, `Trace89Centre.gnat`, `gnat_bound` |
| `Trace89Syntax` | literal `TenPositiveTrace89.expression`, `Trace89BFSSyntax.literal_zero_iff` |
| `Trace89ModelIff` | `positive_model_iff` |
| `IPRATrace89` | the iPRA endpoints |
