# iPRA endpoints for package 170's 13-positive 72/154 q⁴ residue carrier

Package 170 (`con-zfc-diophantine-forms/170-quotient-carriers/compact`) supplies
`fixed_13_residue_q4_72_degree154.json`: thirteen positive unknowns
`J, F, α, z, f, n, i, T, s, w, η, ζ, γ`, 72 operations, exact degree 154
(proof: `FIXED_CARRIER_PROOF.md` §6.1). It is the reduced 71/162 residue
carrier (record `research/p170-71-endpoint`) with exactly two changes:

* the auxiliary carrier reads its residue modulo `q⁴` instead of `E`:
  `t = q⁴ n - k + R` (`q4 = q2 · q2`);
* the strong multiplier is scaled by `q²` instead of `E`: `m = q² i A`.

Everything else (`N1`, `Nt`, `Ns = f² - I S`, `Q = Δ (f² - 1)`,
`B = Q (t² - A V²) - t² + A`, `P = N1 · Nt · (3 B + 1) · Ns - 1`) is unchanged.
The `coefficient_binding` names the four direct-BFS943 raw hashes of
`trace75_degree402.json`, as does `compact/COEFFICIENTS.json`; the endpoint uses
`IPRATrace75`'s ports.

The Lean endpoints are in `Lean/DiophantineConsistency/BFS943/IPRAQuot170p72.lean`
(namespace `DiophantineConsistency.IPRAQuot170p72`): `positiveBridge`,
`native_equivalence`, `standard_equivalence`, `reference_equivalence`,
`standard_translated_equivalence`, `reference_translated_equivalence`, with
`expression : Expr (Fin 13)` and
`expression_def : expression = Q170Form72.expression (fun j => (fixedPorts j : ℤ))`.
Each depends only on `propext`, `Classical.choice`, `Quot.sound`.

## Route

The proof is the 71 route of `research/p170-71-endpoint` with the modulus `q⁴`
(the 71 modules `Q170Sound71`, `Q170Complete71` were transcribed mechanically,
and only the modulus-dependent steps changed):

**Soundness** (`Q170Sound72.equations_of_zero`). Units, the multiplier square
(`A ∣ S` still holds, as `A ∣ m`), `A = τ²` and `y = |t| / τ` are as before.
Now `q⁴ ∣ 4 S²` (as `q² ∣ m`), so `y ≡ ±1 (mod q⁴)`; `q⁴ ∣ E` gives
`τ ≡ 1 (mod q⁴)`, so `t = ±τ y` gives `k - R ≡ ±1 (mod q⁴)`. The rank window
`ArithmeticAdaptiveRankWindow2011.scalar_rank_window` gives
`R + q³ + q + 1 ≤ q⁴`, hence `R + 2 < q⁴`. `Q170Residue.carrier_of_residue`
is stated for any modulus `M ∣ E` with `R + 2 < M`; at `M = q⁴` it recovers the
main index `R`, excludes `R = 2ν + 1` by growth, and from `2ν = R + 1` and the
*full* first recurrence `k = 2ν + 4EYh` gives `k ≡ R + 1 (mod E)` and
Carrier65's carrier `E N + k = τ + R` — the package's "the exact first index
recovers its full modulus afterwards".

**Completeness** (`Q170Complete72.zero_of_halt`). As for 71, with a strong
multiplier divisible by `A q²` (`m = q² j A`); the fresh auxiliary ordinate is
`≡ -1 (mod 4 I²)` with `q⁴ ∣ I²`, and `E = q⁴ w s`, so
`τ y + k = R + q⁴ n` for the explicit positive natural
`n = 4 G² w₂ + w s (2 Y r₁ y + 4 Y s₁)`.

## Binding check

`check_lean_graph.py` (run `py -I -X utf8 -B check_lean_graph.py`) pins the 72
JSON (`27c22007…`), `COEFFICIENTS.json` (`0fe6f625…`) and the 75 JSON. It checks
the metadata (thirteen witnesses, 72 operations, degree 154, no dead rows) and
the direct-BFS943 raw hashes, compares the output of `value72` and 16 named
rows (including `q4`) with the JSON after exact commutative-ring structural
normalization, rejects 14 single-gate mutations (among them the modulus `q³`,
the multiplier `q i A` and the carrier sign), and checks the literal, the
endpoint definitions and `fixedPorts` verbatim. Output: `check-output.json`.
These are finite external checks, not Lean theorems about files.

## New modules (all in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `Q170Syntax72` | `Q170Form72.value72`, `expression`, `evalRing_expression`, `value72_factors`; `Q170Syntax72.literal_zero_iff` |
| `Q170Sound72` | `equations_of_zero`, `zero_halts` |
| `Q170Complete72` | `zero_of_halt` |
| `IPRAQuot170p72` | the iPRA endpoints |

It reuses `Q170Residue` and `Q170Units` (record `research/p170-71-endpoint`)
and the Carrier65 calibration `research/bfs943-carrier65-calibration`.

## Scope and non-claims

The endpoints are about the Lean literal at the symbolic direct-BFS943 ports;
the JSON correspondence and the port hashes are the finite external checks
above. The exact-degree certificate (§8) is not formalized.
`maxHeartbeats 1000000` (file level) in `Q170Sound72` and `Q170Complete72`;
none is `0`.
