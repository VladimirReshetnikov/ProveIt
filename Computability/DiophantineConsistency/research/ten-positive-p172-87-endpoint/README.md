# iPRA endpoints for package 172's ten-positive 87/214 free-inverse circuit

Package 172 (`con-zfc-diophantine-forms/172-pooled-powers-round21`) supplies
the ten-positive circuit
`part2/ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/positive10/positive10_degree214_ops87.json`
(mode `free_inverse`, 87 operations, exact degree 214, weight `L = bV`; proof:
`PROOF.md` in the same folder, §1–§6). In the notation of that proof, with
`h = β J`, `q = h + 1`, `C = q - F - α`, `k = η + ζ`:

* `Wbase = w`, `X = q w`, `λ = q`: the Pell base is `A = q s (X + 1) + 1` and
  the first parameter `v = X (q s)²`;
* the strip is free: `c = k s + η` (`Y = s`);
* `D = 6 q⁷` and the inverse-Lucas offset
  `eclear = 6 (e - q⁴ s) - v k (k² - 4)` with `e = k - R - 1`;
* `B = (K0 + w) C - F`, `V = f (c T - R) - c`, `L = b V`,
  `Z = h D [H (n - L B) + K] - H [D B + h eclear]`, `M = h D H`.

The `coefficient_binding` equals the 75/402 graph's in every port field
(only the relative `path` differs): the direct-BFS943 tuple, K0 raw
`0a86821a…`, MC `6007cabd…`, MF `48333b0d…`, β `0664a868…`.

The Lean endpoints are in `Lean/DiophantineConsistency/BFS943/IPRATrace87.lean`
(namespace `DiophantineConsistency.IPRATrace87`): `positiveBridge`,
`native_equivalence`, `standard_equivalence`, `reference_equivalence`,
`standard_translated_equivalence`, `reference_translated_equivalence`, at the
same ports `fixedPorts` as `IPRATrace75`. Each depends only on `propext`,
`Classical.choice`, `Quot.sound`.

## Route

Soundness goes through the zero-free boundary of
`research/bfs943-fixed-source-entry` (`BFS943FixedSource.FixedSource`), as for
82/240; completeness builds a fresh 87 zero from the halting packing.

**Registers.** `TenPositiveTrace87.regs` is `TenPositiveTrace82.regsAtC p v X Y W c`
at `X = q w`, `Y = q s`, `W = w`, `c = k s + η`, with `D = 6 q⁷`, `Z`, `M`
replaced by a structure update; `ecl p v` is the offset `eclear`.

**The inverse-Lucas layer** (`InverseLucasCubic`, reusable; nothing in it is
specific to 87):

* `second_order`: at the Pell base `b + 2 = 2P + 1`, by internal Σ₁ induction,
  `x_n = 1 + 2P n² + P² W`, `y_n = n + 4P C + P² Z` with `6 C + n = n³`
  (`C = binom(n+1, 3)`). Only the residue modulo `P²` is used: neither the
  sign nor the size of `Z_m` is needed;
* `cubic_split`/`pell_cubic_split`: `6 (k + Δ) - P k (k² - 4) = 6 u` and
  `3 u = 3 (2 n + Δ) + P² w` for `k = 2 y_n` and any `Δ` (the identity
  `3 (e* - d₀) = 4 v² [24 Z_m - A_m S_m]` with the denominator cleared; the
  factor `6` of `k (k² - 4)` comes from `3 ∣ d³ - d`, `cube_three`);
* `cancel_three`: `q^(m+1) ∣ 3 x ⇒ q^m ∣ x` for every `q` (cases `3 ∣ q` and
  `q² ≡ 1 mod 3`), so the case `3 ∣ q` costs one power;
* `pow2_cancel_signed_odd` (a power of two cancels any signed odd factor) and
  `positive_carrier_signed` (the reverse carrier coordinate at a signed offset
  quotient).

**Norm layer** (`Trace87Factors` … `Trace87NormRank`): mechanical copies of
the 82 modules with `X = q w`. Here `q⁴ ≤ v` fails (`v = q³ w s²`), so the
bound `2 q⁴ < c` comes from the main index instead
(`Trace87NormRank.two_q4_lt_c`: `c = ψ_A(r) ≥ ψ_A(3) ≥ 2 A²`, `A ≥ q²`).

**Transport and first index** (`Trace87Transport`, `Trace87NormOffset`):
`B ≥ 0` by the carrier contradiction with `2 eclear ≤ 12 (e - q⁴ s) < bV D`
(the cubic term is nonnegative as `k ≥ 2`). At the first index `n`
(`k = 2 ψ_{1+2v}(n)`), `eclear = 6 u`; the carrier gives `6 q⁷ ∣ h H (6 u)`,
so `q⁷ ∣ u` (the literal `6` is cancelled, not inverted mod `q`); with
`q⁶ ∣ v²`, `3 (2n - R - 1 - q⁴ s) ≡ 0 (mod q⁶)` and `cancel_three` give
`q⁴ ∣ 2n - R - 1`, hence `2n = R + 1` (`|2n - R - 1| < q⁴`). This is the
order of the package proof: no power-of-two property of `q` is used here.

**Projection** (`Trace87Projection`, `Trace87GraphPower`): `H ∣ 6 h K` (seven
cancellations of `q`; the `6` is kept), the whole-product projection with
multiplier `6 h X`, and `Trace87ProductPower.whole_product_lt_power_cube`
(multiplier `≤ X³`, `r ≥ 25`) give `X = 2^R`.

**Integral** (`Trace87Integral`): with `2n = R + 1`,
`3 u = q⁴ s (X² s³ w - 3)` and `q⁷ ∣ u` give `q³ ∣ s (X² s³ w - 3)`; `X` is
even, so `pow2_cancel_signed_odd` gives `q³ ∣ s`. `H ∣ K` and
`eclear = 6 q⁷ (u / q⁷) = D ρ` in the carrier give `h ∣ B`, the natural
transport `(K0 + w) C = F + h t`.

**Soundness = FixedSource** (`Trace87Source.source_of_zero`) at
`sourceVal p v = ![J, F, α, 1, 1, w, 1, 1, 1, 1]`, exactly as in 82 with the
transport base `w`; then `FixedSourceHalt.source_halts`.

**Completeness** (`Trace87HaltGraph.halt_zero_of_model_ports`): the packing's
transport base `2^{R - uN}` is the 87 coordinate `w` itself (`X = q w = 2^R`).
`Trace87ReverseData` applies `TenPositiveScaledReverseStart.scaled_start` at
scale `μ = q`; at the first index `r + 1` the cubic split gives
`eclear = 6 u` with `3 (u + μ⁴ Y) = P² w`, and `μ⁸ ∣ P²`, `μ⁴ Y = μ⁷ s_Y` give
`u = μ⁷ ρ` with `ρ` integral but possibly negative. The bound
`-ρ ≤ μ⁴ Y + P K³ < f` (`Trace87ReverseData.seed_large`) with `κ < f` and
`τ ≥ 2` makes `n = τ f y + (1 + b L) t + ρ - κ` positive. `Trace87ParentMap`
and `Trace87ReverseGraph` give the positive 87 zero.

`Trace87ModelIff.positive_model_iff` joins both directions; the iPRA
wrappers are those of `IPRATrace75`.

## Binding check

`check_lean_graph.py` (run `py -I -X utf8 -B check_lean_graph.py`) pins the
87 and 75 JSON graphs, `TenPositiveTrace75.lean`, `Trace79Regs.lean` and
`Trace82Regs.lean`; checks the graph metadata, no dead rows, and the port
binding (equal to the 75 graph's except `path`, with the four direct-BFS943 raw
hashes); checks that `regsAt` is the parameterized 75 register map and
`regsAtC` is `regsAt` with `c` as a parameter; parses `regsAtC`, the 87
instance, lets and structure update in `regs`, and `value87`, and compares the
output with the JSON output after exact commutative-ring structural
normalization (also `X`, `qY`, `c`, `sixq7`, `eclear`, `Bt`, `Znum`, `Mtot`
individually). It rejects seven mutations (denominator `q⁷`; chart
`X = q (q w)`; strip `c = k q s + η`; Pell scale `1`; transport base `q w`;
sign of the `q⁴ s` correction; sign of the inverse cubic), and checks the
literal and endpoint definitions verbatim and that `fixedPorts` is textually
the `IPRATrace75` one, so `reviews/bfs943-source-promotion/tools/check_ports.py`
covers 87 too. Output: `check-output.json`. These are finite external checks,
not Lean theorems about files.

## New modules (all in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `InverseLucasCubic` | the reusable inverse-Lucas layer (above) |
| `Trace87Regs` | `regs`, `ecl`, `value87`, register lemmas |
| `Trace87Factors` | natural representatives (`X = q w`, `D7 = 6 q⁷`) |
| `Trace87Residue` … `Trace87NormKpos` | norm layer (copies of `Trace82*`) |
| `Trace87NormRank` | rank window, main index, `two_q4_lt_c` |
| `Trace87NormOffset` | first-index alignment from the residue hypothesis |
| `Trace87Transport` | `B ≥ 0`, mask, `eclear = 6 u`, `q⁷ ∣ u`, `q⁴ ∣ 2n - R - 1` |
| `Trace87Projection` | `H ∣ 6 h K`, whole-product projection, `zero_alignment` |
| `Trace87VariableHeight`, `Trace87ProductPower`, `Trace87GraphPower` | `X = 2^R` |
| `Trace87Unweighted` | `H ∣ K` |
| `Trace87Integral` | `q³ ∣ s`, natural transport `(K0 + w) C = F + h t` |
| `Trace87Sandwich` | both scaled Pell sandwiches at the free strip |
| `Trace87Source` | positive 87 zero ⇒ `FixedSource` |
| `Trace87ParentMap` | squared-trace parent and its positive shift |
| `Trace87ReverseData` | scaled reverse data with the signed inverse offset |
| `Trace87ReverseGraph` | source data ⇒ positive 87 zero |
| `Trace87HaltGraph` | halting ⇒ positive 87 zero |
| `Trace87Syntax` | literal `TenPositiveTrace87.expression`, `Trace87BFSSyntax.literal_zero_iff` |
| `Trace87ModelIff` | `positive_model_iff` |
| `IPRATrace87` | the iPRA endpoints |
