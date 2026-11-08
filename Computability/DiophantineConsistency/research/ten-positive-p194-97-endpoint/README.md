# iPRA endpoints for package 194's ten-positive 97/202 `quotient_t` circuit

Package 194 (`con-zfc-diophantine-forms/194-guarded-resultants-early-projection`)
supplies, in `positive/`, three root-scale centred versions of package 172's
87/214 free-inverse chart (proof: `positive/PROOF.md` §§1–6). This record
covers `quotient_t_radix67.json` (mode `quotient_t`, 97 operations, exact
degree 202, weight `L = bV`, root scale `r = 2`) and the shared root-scale-two
layer; the companion `product2_radix67.json` (111/198) is
`research/ten-positive-p194-111-endpoint`. Only the `_radix67` copies are on
the direct-BFS943 tuple; the `_low2963` copies are a different tuple and
`product4` (119/190, square transport, root scale 4) is not covered.

In the notation of `research/ten-positive-p172-87-endpoint` (the Lean register
`Y = q s` is package 194's `Ybar`, `Am1 = A - 1`), the circuit

* replaces the 87 transport gate `n - b V B` by `n - V (b B + C2)` at the
  quotient centre `C2 = 2 A U E - U Qt`, `Qt = (k Ybar) [ell + k - (k Ybar) Ybar]`
  (JSON rows `cy`, `cyy`, `qt_inner`, `Qt`, `twoA = Am1 + Ap1`, `twice_upper`,
  `UQt`, `center_root`, `bB`, `bB_center`, `LBt`), so `Z = Z₈₇ - M (C2 V)`;
* replaces `G` by `4 G` in the norm (rows `scaledG`, `RG`):
  `P = Q (Z² - 4 M² G V²) + (4 M² G - Z²)`.

The `coefficient_binding` equals the 75/402 graph's in every port field except
the relative `path` and an explicit `endianness: little` annotation: the
direct-BFS943 tuple, K0 raw `0a86821a…`, MC `6007cabd…`, MF `48333b0d…`,
β `0664a868…`.

The Lean endpoints are in `Lean/DiophantineConsistency/BFS943/IPRATrace97.lean`
(namespace `DiophantineConsistency.IPRATrace97`): `positiveBridge`,
`native_equivalence`, `standard_equivalence`, `reference_equivalence`,
`standard_translated_equivalence`, `reference_translated_equivalence`, at the
same ports `fixedPorts` as `IPRATrace75`, with `expression_def :
expression = TenPositiveTrace97.expression (fun j => (fixedPorts j : ℤ))`.
Each depends only on `propext`, `Classical.choice`, `Quot.sound`.

## Route

The circuit is not an `n`-shift of 87: its roots are `z = ±2 g y`, not
`±g y`. The route reduces the root scale before anything else and then ends in
the shifted 87 chain of `research/ten-positive-p179-89-endpoint`
(`Trace87Shift*`, which reads the carrier only modulo `D` and `H`, ending in
`BFS943FixedSource.FixedSource` and `FixedSourceHalt.source_halts`).

**Root scale two** (`Scaled87Regs`, `Scaled87Sign`). `scaledNorm r Z` is the
polynomial above; `scaledNorm r (2 Z') = 4 normValue r Z'`. Package 194's
root extraction (§2) is read through parity: `Q = 4 Δ a F0`, so `Q - 1` is
odd and a zero has `Zc² = 4 (…)`, hence `Zc = 2 Zh` (`even_of_sq`, by
`div_add_mod` in the model) with `Zh` a zero of the unscaled 87 norm.
`Trace87NormRoots.graph_adjacent` (generic in the carrier) then gives
`Zh = M z`, `z = ±τ f y`, and the adjacent Pell norm at `|V|`.

**Sign** (`Scaled87Estimate`, `Scaled87Sign.shift_zero`), package 194 §§4–5
for an arbitrary shift `ws` with `Zc = Z₈₇ - M ws`, under the single
hypothesis `ws ≤ 5 g |V|` (`g = τ f`, no sign assumed):
`Scaled87Estimate.sixtyfour_le` gives `64 g ≤ F = 1 + 2a` from `D U² ≥ 1024`
(`D ≥ 16`, `U ≥ c² ≥ 9`), so `F |b| > F²/2` gives `|b| > 32 g`, and
`scaled_estimate` gives `2 (2 g y + ws) < b V` (`y < 2 |V|`). The 87 carrier is
`M (2 z + ws)`, and `TenPositiveCarrierTransport.model_nonnegative_of_carrier`
(offset bound `2 eclear < b V D` as in 87) gives `B ≥ 0` at the positive `n`
of the zero itself. Then `Z₈₇ - M (ws + z) = Zh` is an 87 zero, i.e.
`Trace87ShiftTransport.ShiftZero p v (ws + z)`. No early `p = 3` projector
and no index-three exclusion is needed for this weight: package 194 itself
notes (end of §3) that its weaker inherited bound already suffices for the
`bV` rows; here `|b| > 32 g` comes from the norm alone.

**The centre** (`Trace97Regs`, `Trace97Centre`). At positive inputs
`Qt = k² Ybar ((X - 1) Ybar² + 1) ∈ [0, E]`, so
`(2A - 1) U E ≤ C2 ≤ 2 A U E` and
`9 G - (2 A U E)² = 9 E + (U E)² (5 A² - 9) > 0`, i.e. `0 ≤ C2 < 3 g`
(package 194's (8)–(9)); `centre_shift` is the hypothesis `C2 V ≤ 5 g |V|`.

**Completeness** (`Scaled87Complete.scaled_zero`), package 194 §6 without
fixing the sign of the 87 root: a halting time gives a positive 87 zero
(`Trace87HaltGraph.halt_zero_of_model_ports`) with `V > 0`
(`Centred87Complete.V_positive`) and `Z₈₇ = M z`, `z = ±g y`
(`Trace87Transport.graph_zero_data`). With the natural shift `W = C2 V`, put
`n' = n + W + g y` (if `z = g y`) or `n' = n + W + 3 g y` (if `z = -g y`); then
`Z₈₇(n') - M W = ±2 Z₈₇(n)` and the scaled norm is `4 value87 = 0`. The
centre does not read `n` (`value97_update`).

`Trace97ModelIff.positive_model_iff` joins both directions; the iPRA wrappers
are those of `IPRATrace75`.

## Binding check

`check_lean_graph.py` (run `py -I -X utf8 -B check_lean_graph.py`) pins the
97 JSON, package 172's 87 JSON (also checking the JSON's `parent.sha256`), the
75 JSON (port binding), the 87 record's checker (whose parser and normalizer
it imports) and the Lean sources that checker reads (`TenPositiveTrace75.lean`,
`Trace79Regs.lean`, `Trace82Regs.lean`, `Trace87Regs.lean`) and
`Centred87Regs.lean`. It checks the graph metadata (including
`root_scale: 2`) and that the JSON rows differ from the 87 rows exactly by the
centre, transport and `4 G` gates; transcribes `value87` with the 87 checker
(re-checked against the 87 JSON), then parses `centre`, `regsAt` and `value97`
into the same interned DAG and compares with the JSON output after exact
commutative-ring structural normalization (also the rows `Qt`, `center_root`,
`bB_center`, `LBt`, `scaledG`, `RG`, `Znum`, `Mtot`, `sixq7`, `eclear`). It
rejects six mutations (root scale 1, root scale 2 only inside the bracket,
centre sign `+ U Qt`, `2A - 1` for `2A`, `Qt` without `k Ybar`, the uncentred 87
gate), checks the literal and endpoint definitions verbatim and that
`fixedPorts` is textually the `IPRATrace75` one, so
`reviews/bfs943-source-promotion/tools/check_ports.py` covers this circuit.
Output: `check-output.json`. These are finite external checks, not Lean
theorems about files.

## New modules (all in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `Scaled87Regs` | `scaledNorm`, `scaledNorm_two`, `regsW` (gate `n - b V B - ws`), `Z_update` |
| `Scaled87Estimate` | `scaled_estimate`, `sixtyfour_le` (ordered rings) |
| `Scaled87Sign` | `even_of_sq`, `shift_zero` (root scale two ⇒ `ShiftZero`) |
| `Scaled87Complete` | `cast_update`, `scaled_zero` |
| `Trace97Regs` | `centre`, `value97`, `value97_eq`, `value97_update`; `Trace97Centre.centre_bounds`, `centre_shift` |
| `Trace97Syntax` | literal `TenPositiveTrace97.expression`, `Trace97BFSSyntax.literal_zero_iff` |
| `Trace97ModelIff` | `positive_model_iff` |
| `IPRATrace97` | the iPRA endpoints |

`Scaled87*` are shared with the 111/198 record.

## Scope and non-claims

The endpoints are about the Lean literal at the symbolic direct-BFS943 ports;
the JSON correspondence and the port hashes are the finite external checks
above. The `_low2963` calibration, `product4` and package 194's natural and
integer equations are not covered. Package 194's early `p = 3` projector
(§3) is not formalized; it is not needed for the `bV` weight.
