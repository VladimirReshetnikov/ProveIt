# iPRA endpoints for package 170's 12-positive 74/438 rational carrier

Package 170 (`con-zfc-diophantine-forms/170-quotient-carriers/compact`) supplies
`fixed_12_rational_74_degree438.json`: twelve positive unknowns
`J, F, α, z, n, i, T, s, w, η, ζ, γ`, 74 operations, exact degree 438
(proof: `FIXED_CARRIER_PROOF.md` §7). On the Carrier65 outer front it deletes
the carrier coordinate, the strong abscissa `f` and the auxiliary ordinate:

* `m = i (a + 2) D`, `S0 = m Δ c²`, `I = m c²`, `W = A (I S0)`,
  `F2 = 1 + W` (the strong abscissa squared), `Q = Δ W`,
  `V = F2 (c T - R) - c`, `G = A F2`;
* the rational carrier `t = E n + e`, `e = k - R - 1` (the substitution
  `t = n + e / E` cleared by `E²`);
* `B = Q (t² - E² G V²) - t² + E² G` and `P = N1 · Nt · (3 B + 1) - 1`.

The `coefficient_binding` names the four direct-BFS943 raw hashes of
`trace75_degree402.json`, as does `compact/COEFFICIENTS.json`; the endpoint uses
`IPRATrace75`'s ports.

The Lean endpoints are in `Lean/DiophantineConsistency/BFS943/IPRAQuot170p74.lean`
(namespace `DiophantineConsistency.IPRAQuot170p74`): `positiveBridge`,
`native_equivalence`, `standard_equivalence`, `reference_equivalence`,
`standard_translated_equivalence`, `reference_translated_equivalence`, with
`expression : Expr (Fin 12)` and
`expression_def : expression = Q170Form74.expression (fun j => (fixedPorts j : ℤ))`.
Each depends only on `propext`, `Classical.choice`, `Quot.sound`.

## Route

Both directions go through the Carrier65 calibration at the same ports
(`research/bfs943-carrier65-calibration`).

**Soundness** (`Q170Sound74.equations_of_zero`, in the ring of differences;
§7.1–§7.2).

1. *Units* (`units_three`): `N1 = Nt = 3 B + 1 = 1`, so
   `(Q - 1) t² = E² A F2 (Q V² - 1)` with `V ≠ 0`.
2. *Coprimality* (20). `A ∣ Q` gives `A` coprime to `Q - 1` and `Q V² - 1`.
   For `F2`: with `W = (a + 2) D L`, `W = F2 - 1`, `Δ + 1 = (a + 2)²` and
   `D² = 1 + Δ c²`, the identities
   `F2 (Δ (DL)² - F2 + 2) - (Q - 1)(DL)² = 1` and
   `F2 (Z M² - F2 + 2) - (Q V² - 1) M² = 1` (`M = (a + 2) L`,
   `Z = Δ (F2² u² - 2 F2 u c + c² - F2 u² + 2 u c)`, `u = c T - R`) are checked by
   `linear_combination` and turned into natural Bézout certificates
   (`bez_of_ring`, `bez_mul`). So `A F2` is coprime to `(Q - 1)(Q V² - 1)`,
   `TenPositiveScaledSquare.scaled_product_factor_square` makes `A F2` a
   square, and `ModelProductPell.pp_square_of_coprime` (with `F2 ≡ 1 (mod A)`)
   gives `A = τ²` and `F2 = f²`.
3. *Rational adjacent-Pell integrality*
   (`TenPositiveAdjacentInteger.quotient_of_scaled_norm`, the inherited lemma of
   §7.1): `Q (E τ f |V|)² = (E τ f)² + (Q - 1) t²` gives `|t| = E τ f y` and
   `Q V² - (Q - 1) y² = 1` with `y` natural. As `n ≥ 1` and `R + 2 < E`,
   `t > 0`, so `t = E τ f y` and `E ∣ k - R - 1`: `k ≡ R + 1 (mod E)`.
4. `Q170Residue.carrier_of_residue` (case `+1`) gives `E N + k = τ + R`.

The Carrier65 solution is `(J, F, α, z, f, τ m, T, s, w, N, η, ζ, y, γ)`
(strong `f² = 1 + Δ (τ m c²)²`, auxiliary `S = Δ τ m c²` with `S² = Q`).

**Completeness** (`Q170Complete74.zero_of_halt`, §7.3). From
`Carrier65BFSHalt.halt_outer`: `τ² = A`, `τ = 1 + 2EYr₁` and
`k = R + 1 + E (4 Y s₁)`. A fresh strong seed whose multiplier is divisible by
`τ (a + 2) D` (`ArithmeticThirteenSeed.strong_index`) gives the multiplier
`τ m`, `m = j (a + 2) D`, and `F2 = 1 + A Δ (m c²)² = f²`; its fresh auxiliary
seed gives `y`, `T` and `V` (`= u > 0`). Since `τ f y ≥ τ > k > 4 Y s₁`,
`n = τ f y - 4 Y s₁` is positive, `t = E τ f y`, and with `Q = S²`,
`G = τ² f²` all three factors are one. The literal zero is
`(J, F, α, z, n, j, T, s, w, η, ζ, γ)`.

## Binding check

`check_lean_graph.py` (run `py -I -X utf8 -B check_lean_graph.py`) pins the 74
JSON (`28bfcd4a…`), `COEFFICIENTS.json` (`0fe6f625…`) and the 75 JSON. It checks
the metadata (twelve witnesses, 74 operations, degree 438, no dead rows) and
the direct-BFS943 raw hashes, compares the output of `value74` and 19 named
rows (including `e`, `mult`, `W`, `f2`, `G`, `E² G`) with the JSON after exact
commutative-ring structural normalization, rejects 14 single-gate mutations,
and checks the literal, the endpoint definitions and `fixedPorts` verbatim.
Output: `check-output.json`. These are finite external checks, not Lean
theorems about files.

## New modules (all in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `Q170Syntax74` | `Q170Form74.value74`, `expression`, `evalRing_expression`, `value74_factors`; `Q170Syntax74.literal_zero_iff` |
| `Q170Sound74` | `bez_of_ring`, `ring_of_bez`, `bez_mul`, `units_three`, `equations_of_zero`, `zero_halts` |
| `Q170Complete74` | `zero_of_halt` |
| `IPRAQuot170p74` | the iPRA endpoints |

It reuses `Q170Residue` and `Q170Units` (record `research/p170-71-endpoint`)
and the Carrier65 calibration `research/bfs943-carrier65-calibration`.

## Scope and non-claims

The endpoints are about the Lean literal at the symbolic direct-BFS943 ports;
the JSON correspondence and the port hashes are the finite external checks
above. The exact-degree certificate (§8) is not formalized. The package's
remark that the residue argument does not extend to this anchored case is
respected: the soundness proof uses the rational integrality, not a residue of
`f`. `maxHeartbeats 1000000` (file level) in `Q170Sound74` and
`Q170Complete74`; none is `0`.
