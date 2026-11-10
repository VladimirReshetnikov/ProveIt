# iPRA endpoints for package 163's ten-positive 80/258 circuit

Package 163 (`con-zfc-diophantine-forms/163-trace-radical`) supplies the
ten-positive circuit `compact/equations/trace80_degree258.json`: chart `q1`,
transport weight `L = bV`, 80 operations, exact degree 258 (proof:
`compact/PROOF.md`, chart table in §2). Relative to the 79/290 circuit
(chart `q2`) it changes four rows, each checked row by row:

* `Y = q s` instead of `q² s`;
* a new row `Wbase = q w`, used in `X = q Wbase` (so `X = q² w` instead of
  `w q`) and in `K0w = K0 + Wbase` (transport base `q w` instead of `w`);
* the denominator `D = q⁴ q² = q⁶` instead of `q⁴ q`.

The offset in the carrier is the 79 one, `N = e - q⁴ s`. So `M = h q⁶ H`,
`Z = h q⁶ [H (n - bV B) + K] - H [q⁶ B + h (e - q⁴ s)]`,
`B = (K0 + q w) C - F`. The `coefficient_binding` is identical to the 75/402
graph's (the direct-BFS943 tuple: K0 raw `0a86821a…`, MC `6007cabd…`,
MF `48333b0d…`, β `0664a868…`).

The Lean endpoints are in
`Lean/DiophantineConsistency/BFS943/IPRATrace80.lean`
(namespace `DiophantineConsistency.IPRATrace80`): `positiveBridge`,
`native_equivalence`, `standard_equivalence`, `reference_equivalence`,
`standard_translated_equivalence`, `reference_translated_equivalence`, at the
same direct-BFS943 ports `fixedPorts` as `IPRATrace75`. Each depends only on
`propext`, `Classical.choice`, `Quot.sound`.

## Route

**Registers.** `TenPositiveTrace80.regs` is the q1 instance of
`TenPositiveTrace79.regsAt p v X Y W` (`X = q (q w)`, `Y = q s`, `W = q w`)
with `D`, `Z`, `M` replaced by a structure update; no new register map.

**The q1 carrier-generic layer** (`Trace80Factors`, `Trace80Residue`,
`Trace80NormRoots`, `Trace80NormFold`, `Trace80NormKpos`, `Trace80NormRank`,
`Trace80NormOffset`) is generated from the q2 copies of the 79 record by a
mechanical substitution: across these seven modules the chart enters only
through the definitions of `X`, `Y` in `Trace80Factors`, the positivity
lines `0 < Y`, `0 < X`, the radix bound `2 q⁴ < c` (now from `q⁴ ≤ X Y²`
directly) and the first-index modulus witness `q⁴ ∣ 2 X Y²`
(`2 X Y² = q⁴ (2 w s²)`). The same holds for `Trace80Transport` (denominator
`q⁶`, `cancel_one_mod_sixth`, mask with transport base `q w`).

**Why chart q1 needs the projection layer.** At a positive zero the carrier
gives `q⁶ ∣ e - q⁴ s` and the first-index alignment gives `e = 4 X Y² σ =
q⁴ s (4 w s σ)`, hence only `q² ∣ s (4 w s σ - 1)`. (In chart q2 `X Y²` carries
`q⁵`, which is why the 79 record could skip `X = 2^R`.) Here `q² ∣ s` needs
`q` to be a power of two, which comes from the projection layer, ported to
chart q1:

* `Trace80Projection`: `H ∣ q⁶ (h K)` from `Z = M z`; since
  `H = q (4 s (X + 1)) - 1`, six applications of
  `Trace75Projection.cancel_base` give `H ∣ h K`, so `H ∣ (h X) K`; then the
  whole-product divisibility, as in `Trace75GraphProduct`;
* `Trace80VariableHeight`, `Trace80GraphPower`: `Trace75VariableHeight` and
  `Trace75GraphPower` over the q1 rank and alignment (the generic
  `Trace75ProductPower`, `Trace75ProductHeight` are reused), giving
  `X = 2^R`.

**Soundness is a zero map to 75** (`Trace80ToTrace75`): `q ∣ X = 2^R` gives
`Pow2 q` (Foundation's `Pow2.of_dvd`), so `q` is even and `a = u + q² - 1`
(`u = 4 w s σ`) is odd with `q² ∣ a s`; `Trace80Parity.pow2_cancel_odd`
(the gcd certificate of `a` and `q²` is a power of two dividing an odd number,
hence `1`) gives `s = q² s'`. At `(…, q w, s', n', …)` the q3 chart has
`X = (q w) q`, `Y = q³ s' = q s` and transport base `q w`: the 75 registers
are `regsAt` at the 80 `X, Y, W` (`regs75_moved`). With `g = τ f y`,
`ρ = 4 Y σ` (`e = XY ρ`) and `N = q⁶ μ`, the coordinate
`n' = n + (g - z) + (V² - bV) B + ρ - μ` makes the 75 carrier `M75 g`, the 75
output is `M75²` times the bracket that vanishes at the 80 zero, and
`h H n' > 0` exactly as in `Trace79ToTrace75`. Then
`Trace75BFSModelHalt.graph_halts`.

**Completeness is a zero map from 76** (`Trace80FromTrace76`): at a positive
76 zero `(…, w, s, n, …)`, the carrier quotient, `B ≥ 0`, `bV ≥ 0`,
`e = 4 X Y² σ` and `σ ≥ 1` are obtained as in `Trace79FromTrace76`. In
addition, `Trace75RadixAlignment.graph_radix_alignment` at the moved 75 zero
(with `β + 1 = 2^590069`, supplied in `Trace80ModelIff`) gives
`q = 2^{dN}`, `w = 2^{R - dN}`, and `dN < 2^{dN} = q`, `3 q < R` give
`w = q w''`. At `(…, w'', q² s, n'', …)` the q1 `regsAt` is the q3 one at
`(…, w, s, …)` (`regsAt_moved`), the offset is `e - q⁶ s = q⁶ μ` with
`μ = 4 w q s² σ - s ≥ 0`, and `n'' = n + (g - z) - ρ + μ` makes the 80
carrier `M80 g`.

## Binding check

`check_lean_graph.py` (run `py -I -X utf8 -B check_lean_graph.py`) pins the
80, 79 and 75 JSON graphs, `TenPositiveTrace75.lean` and `Trace79Regs.lean`;
checks the row difference from 79 listed above; checks that the body of
`regsAt` is the body of `TenPositiveTrace75.regs` with the `Y`, `X`, `s` lets
removed and `W` for `w` in `B`; parses `regsAt`, the q1 instance and
structure update in `regs`, and `value80`, and compares the output with the
JSON output after exact commutative-ring structural normalization (also `X`,
`Y`, `D`, `B`/`Bt`, `Znum`, `Mtot` individually). It rejects four mutations
(denominator `q⁵`; `Y = q² s`; transport base `w`; sign of the `q⁴ s`
correction), checks the literal and endpoint definitions verbatim, that
`fixedPorts` is textually the `IPRATrace75` one, and that the 80
`coefficient_binding` equals the 75 one, so
`reviews/bfs943-source-promotion/tools/check_ports.py` covers 80 too.
Output: `check-output.json`. These are finite external checks, not Lean
theorems about files.

## New modules (all in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `Trace80Regs` | q1 `regs`, `value80`, register lemmas |
| `Trace80Factors` | natural representatives (`X = q² w`, `Y = q s`, `M = h q⁶ H`), `firstParam` |
| `Trace80Residue` | `c_eval`, signed residue |
| `Trace80NormRoots` | roots, adjacent Pell at an arbitrary carrier (q1) |
| `Trace80NormFold` | first/doubled Pell, indices, odd ordinate (q1) |
| `Trace80NormKpos` | first index `≥ 2`, radix size, `K > 0` (q1) |
| `Trace80NormRank` | rank window, auxiliary/main index, exact rank (q1) |
| `Trace80NormOffset` | first-index alignment, exact offset (q1) |
| `Trace80Transport` | `graph_bv_bound`, `graph_zero_data` (`q⁶ ∣ e - q⁴ s`) |
| `Trace80Projection` | `H ∣ (h X) K`, whole-product divisibility (q1) |
| `Trace80VariableHeight` | variable-base height bound (q1) |
| `Trace80GraphPower` | `X = 2^R` (q1) |
| `Trace80Parity` | cancelling an odd factor against a power of two |
| `Trace80ToTrace75` | positive 80 zero ⇒ positive 75 zero |
| `Trace80FromTrace76` | positive 76 zero ⇒ positive 80 zero |
| `Trace80Syntax` | literal `TenPositiveTrace80.expression`, `Trace80BFSSyntax.literal_zero_iff` |
| `Trace80ModelIff` | `positive_model_iff` |
| `IPRATrace80` | the iPRA endpoints |
