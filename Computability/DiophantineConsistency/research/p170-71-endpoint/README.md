# iPRA endpoints for package 170's 13-positive 71/162 residue carrier

Package 170 (`con-zfc-diophantine-forms/170-quotient-carriers/compact`) supplies
`fixed_13_residue_71_degree162.json`: thirteen positive unknowns
`J, F, α, z, f, n, i, T, s, w, η, ζ, γ`, 71 operations, exact degree 162
(proof: `FIXED_CARRIER_PROOF.md` §§1–6, the reduced form (4)). It is the
Carrier65 outer front (`q = βJ + 1`, `X = w q`, `Y = s q³`, `E = X Y`,
`k = η + ζ`, `ℓ = E k Y`, `c = k Y + η`, `a = E + Y`, `H = 4a + 3`,
`Δ = a² + H`, `D = X + a c + γ H`, the rank `R` and the transport) with
Carrier65's carrier coordinate deleted:

* the first radicand `A = 1 + ℓ (ℓ + k)` is not a norm factor;
* the strong multiplier is `m = E i A` (`I = m c²`, `S = m Δ c²`,
  `Ns = f² - I S`, `Q = Δ (f² - 1)`);
* the auxiliary carrier is `t = E n - k + R` and
  `B = Q (t² - A V²) - t² + A`, `V = f² (c T - R) - c`;
* the output is `P = N1 · Nt · (3 B + 1) · Ns - 1`.

The `coefficient_binding` names the four direct-BFS943 raw hashes of
`trace75_degree402.json` (K0 `0a86821a…`, MC `6007cabd…`, MF `48333b0d…`,
β `0664a868…`), as does `compact/COEFFICIENTS.json`; the endpoint therefore uses
`IPRATrace75`'s ports `fixedPorts = ![β, K0, MC, β + MF_native]`.

The Lean endpoints are in `Lean/DiophantineConsistency/BFS943/IPRAQuot170p71.lean`
(namespace `DiophantineConsistency.IPRAQuot170p71`): `positiveBridge`,
`native_equivalence`, `standard_equivalence`, `reference_equivalence`,
`standard_translated_equivalence`, `reference_translated_equivalence`, with
`expression : Expr (Fin 13)` and
`expression_def : expression = Q170Form71.expression (fun j => (fixedPorts j : ℤ))`.
Each depends only on `propext`, `Classical.choice`, `Quot.sound`.

## Route

The bridge goes through the Carrier65 calibration at the same ports
(`research/bfs943-carrier65-calibration`): soundness produces a positive
solution of Carrier65's five equations and calls
`Carrier65BFSSource.equations_halt`; completeness starts from
`Carrier65BFSHalt.halt_outer`.

**Soundness** (`Q170Sound71.equations_of_zero`, in the ring of differences of
the model; `FIXED_CARRIER_PROOF.md` §3–§5).

1. *Units* (`Q170Units.units_four`). The four factors have product one; `N1`
   and `Ns` are `f² - ((a+2)² - 1) t²` forms, never `-1` (mod 4,
   `ModelCarrierScaled.strong_ne_neg_one`), and `3B + 1 ≠ -1` by
   discreteness, so all four are one.
2. *The multiplier square* (`Q170Units.square_extraction`). `Ns = 1` gives
   `Q = S²`, so `B = 0` is `(S² - 1) t² = A (S² V² - 1)`. `V ≠ 0`; with
   `A ∣ S`, explicit Bézout certificates show `A` coprime to
   `(S² - 1)(S² V² - 1)` and to `S² - 1`, so
   `TenPositiveScaledSquare.scaled_product_factor_square` gives `A = τ²`,
   `ArithmeticGcdNormalization.unit_certificate_cancel` and
   `ArithmeticSquareDivisibility.dvd_of_square_dvd` give `τ ∣ |t|`, and
   `y = |t| / τ > 0` satisfies Carrier65's auxiliary norm with `i = m`.
3. *Residues* (`Q170Units.aux_residue`). Internal Pell classification puts
   `(S |V|, y)` on the orbit of base `S`; the index is odd, so
   `y ≡ ±1 (mod 4 S²)` (`ArithmeticOddOrdinateResidue.odd_ordinate_pm`), and
   `E ∣ S`. The first Pell classification gives `τ ≡ 1 (mod E)`. Hence
   `t = ±τ y` gives `k - R ≡ ±1 (mod E)`.
4. *The residue sign* (`Q170Residue.carrier_of_residue`, generic in the
   modulus `M ∣ E` with `R + 2 < M`). With the first index `ν`
   (`τ = x_ν`, `k = 2 y_ν` at base `2EY + 1`), `2ν ≡ R ± 1 (mod M)` forces
   `ν ≥ 12`, so the main index exceeds five and `2R < c`; the signed half-index
   recovery `ArithmeticPellHalfIndex.literal_half_index` gives the main index
   `R`, hence `2ν = R ± 1` exactly. The case `R = 2ν + 1` contradicts
   `c = y_{2ν+1}(a) > 16^ν y_{ν+1}(b) > (2b + 3) y_ν(b)`
   (`ArithmeticPellPowerRecovery.paired_comparison_strict`, `y_lower`) against
   `c < k (Y + 1)`. In the other case `k = R + 1 + 4 E Y h` and
   `τ = 1 + 2 E Y r`, so `N = 2Yr - 4Yh > 0` satisfies `E N + k = τ + R`:
   Carrier65's carrier `τ = E N + k - R`.

The Carrier65 solution is `(J, F, α, z, f, m, T, s, w, N, η, ζ, y, γ)`.

**Completeness** (`Q170Complete71.zero_of_halt`; §6). From
`Carrier65BFSHalt.halt_outer` (the direct-BFS943 packing, transport,
`R ≡ 3 (mod 4)` and the outer seed, whose first root `τ = E n₀ + k - R` has
`τ² = A`), the first Pell residues give `τ = 1 + 2EYr₁` and, at the first index
`(R+1)/2`, `k = R + 1 + 4EYs₁`. A fresh strong seed whose multiplier is
divisible by `A E` (`ArithmeticThirteenSeed.strong_index`, `b = A E`; the
package's matrix-period choice is the internal pigeonhole) gives `m = E j A`,
and its fresh auxiliary seed (`ArithmeticThirteenSeed.auxiliary_seed_of`) has
`y ≡ -1 (mod 4 I²)`, so `E ∣ y + 1`. Then `n = (τ y + k - R) / E` is an
explicit positive natural, `E n - k + R = τ y`, `V` equals the seed's positive
quotient, and all four factors are one. The literal zero is
`(J, F, α, z, f, n, j, T, s, w, η, ζ, γ)`.

## Binding check

`check_lean_graph.py` (run `py -I -X utf8 -B check_lean_graph.py`) pins the 71
JSON (`a2f66863…`), `COEFFICIENTS.json` (`0fe6f625…`) and the 75 JSON
(`8b9b9421…`). It checks the graph metadata (thirteen witnesses in order, 71
operations, degree 162, output `output`, no dead rows), that the circuit's and
`COEFFICIENTS.json`'s raw hashes are the direct-BFS943 ones of the 75 graph,
parses every `let` row and the output of `value71` into the same interned DAG
as the JSON rows and compares after exact commutative-ring structural
normalization (no distribution): the output and 15 named rows (`A`, `c`, `Δ`,
`D`, `N1`, `R`, `t`, `Nt`, `iA`, `S`, `I`, `Ns`, `Q`, `V`, `B`). It rejects 14
single-gate mutations of the Lean text, and checks the literal and endpoint
definitions verbatim and that `fixedPorts` is textually the `IPRATrace75` one,
so `reviews/bfs943-source-promotion/tools/check_ports.py` covers this circuit.
Output: `check-output.json`. These are finite external checks, not Lean
theorems about files.

## New modules (all in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `Q170Residue` | `carrier_of_residue` (the residue sign, generic modulus `M ∣ E`), `large_of_six`, `eq_of_mod_small` |
| `Q170Units` | `units_four`, `three_mul_add_one_ne`, `ι_tsub`, `ι_absdiff`, `square_extraction`, `aux_residue` |
| `Q170Syntax71` | `Q170Form71.value71` (the JSON rows), `expression`, `evalRing_expression`, `value71_factors`; `Q170Syntax71.literal_zero_iff` |
| `Q170Sound71` | `equations_of_zero`, `zero_halts` |
| `Q170Complete71` | `zero_of_halt` |
| `IPRAQuot170p71` | the iPRA endpoints |

`Q170Residue` and `Q170Units` are shared with the 72/154 and 74/438 records.

## Scope and non-claims

The endpoints are about the Lean literal at the symbolic direct-BFS943 ports;
the JSON correspondence and the port hashes are the finite external checks
above. Package 170's exact-degree certificates (§8), its raw 70/206 form and
its verifier are not formalized; the 70/206 raw form has no endpoint here.
`maxHeartbeats 1000000` (file level) in `Q170Sound71` and `Q170Complete71`;
none is `0`. Nothing is claimed about minimality or priority.
