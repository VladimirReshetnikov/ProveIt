# iPRA endpoints for package 163's ten-positive 79/290 circuit

Package 163 (`con-zfc-diophantine-forms/163-trace-radical`) supplies the
ten-positive circuit `compact/equations/trace79_degree290.json`: chart `q2`,
transport weight `L = bV`, 79 operations, exact degree 290 (proof:
`compact/PROOF.md`, chart table in §2). Relative to the 76/352 circuit
(chart `q3`) it changes three things, each checked row by row:

* `Y = q² s` instead of `q³ s` (rows `q4 = q2 * q2` replaces `q3`, `Y = q2 * s`);
* the denominator `D = q⁵` (row `D = q4 * q`) instead of `XY` in `P1mu2` and
  `mu2inner`;
* the offset in the carrier is `N = e - q⁴ s` (rows `shift = s * q4`,
  `eclear = e - shift`, `P1e = bJ * eclear`).

So `M = h q⁵ H`, `Z = h q⁵ [H (n - bV B) + K] - H [q⁵ B + h (e - q⁴ s)]`.
The `coefficient_binding` is identical to the 75/402 graph's (the
direct-BFS943 tuple).

The Lean endpoints are in
`Lean/DiophantineConsistency/BFS943/IPRATrace79.lean`
(namespace `DiophantineConsistency.IPRATrace79`): `positiveBridge`,
`native_equivalence`, `standard_equivalence`, `reference_equivalence`,
`standard_translated_equivalence`, `reference_translated_equivalence`, at the
same direct-BFS943 ports `fixedPorts` as `IPRATrace75`. Each depends only on
`propext`, `Classical.choice`, `Quot.sound`.

## Route

**Registers.** `Trace79Regs.regsAt p v X Y W` is the 75 register map with the
chart coordinates `X, Y` and the transport base `W` (in `B = (K0 + W) C - F`)
as parameters (`regs75_eq`: the 75 map is the q3 instance, by `rfl`). The 79
registers are the q2 instance `X = w q`, `Y = q² s`, `W = w`, with `D`, `Z`, `M`
replaced by a structure update. Because `Y` changes, every norm-side
register changes, so the q3 layer cannot be reused directly.

**The q2 carrier-generic layer** (`Trace79Factors`, `Trace79Residue`,
`Trace79NormRoots`, `Trace79NormFold`, `Trace79NormKpos`, `Trace79NormRank`,
`Trace79NormOffset`) is a copy of `Trace75Factors`, `Trace75Residue` and the
q3 `TraceNorm*` modules (including `TraceNormRank`/`TraceNormOffset` from
the 77 record) over the 79 registers. Only the `Y`-specific steps changed:
`Y > 0` from `q² s`, the radix bound `2 q⁴ < c` (now via `2 q² ≤ k`,
`q² ≤ Y`), the first-index modulus witness `q⁴ ∣ 2 X Y²`, and `M = h q⁵ H`.

**Soundness is a zero map to 75** (`Trace79ToTrace75`):

1. `Trace79Transport.graph_zero_data`: `Z = M z`, `z = ±τ f y`; `B ≥ 0` by the
   generic carrier contradiction at weight `bV`, denominator `q⁵` and offset
   `N < b`; the mask; reducing `Z = h q⁵ H z` mod `q⁵` gives `q⁵ ∣ h H N`,
   hence `q⁵ ∣ N` (`cancel_one_mod_fifth`) and `q⁴ ∣ e`.
2. `Trace79NormOffset.graph_offset_exact`: `e = 4 X Y² σ`; as `X Y² = q⁵ w s²`,
   `q⁵ ∣ e`, so `q⁵ ∣ q⁴ s` and `s = q s'` (`s' > 0`).
3. At `s'` the q3 chart has `Y = q³ s' = q² s`: the 75 registers at
   `(…, s', n', …)` are `regsAt` at the 79 `X, Y, W` (`regs75_moved`). With
   `g = τ f y`, `e = XY ρ` (`ρ = 4 Y σ`) and `N = q⁵ μ`, the coordinate
   `n' = n + (g - z) + (V² - bV) B + ρ - μ` makes the 75 carrier `M75 g`;
   the 75 output is then `M75²` times the bracket
   `Q (g² - G V²) + (G - g²)`, which is zero because the 79 output is `M79²`
   times the same bracket (`norm_bracket`). `h H n' = h H g + h H V² B + H B +
   h H ρ - h K > 0` since `H g > K`.
4. `Trace75BFSModelHalt.graph_halts` gives a halting time of machine 215.

**Completeness is a zero map from 76** (`Trace79FromTrace76`): at a positive
76 zero, `Trace77Transport.graph_bv_bound` and `Trace76Transport` give the
carrier quotient, `bV ≥ 0`, `B ≥ 0`; the moved 75 zero gives
`e = 4 X Y² σ` (`Trace75OffsetExact`), and `Trace75Size` with the rank window
forces `σ ≥ 1`, so `μ = 4 w q² s² σ - s ≥ 0` with `e - q⁵ s = q⁵ μ`. At
`(…, q s, n'', …)` the q2 registers are the 75 registers at `(…, s, …)`
(`moved_fields`), and `n'' = n + (g - z) - ρ + μ` makes the 79 carrier
`M79 g`, so the 79 output vanishes; `h H n'' = h H g + h H bV B + H B + h H μ - h K > 0`.

The PROOF.md route for q2 additionally invokes `X = 2^R` before `D ∣ e`; it
is not needed here, because the first-index alignment alone gives
`e = 4 X Y² σ` and `q⁵ ∣ X Y²` in chart q2.

## Binding check

`check_lean_graph.py` (run `py -I -X utf8 -B check_lean_graph.py`) pins the
79, 75 and 76 JSON graphs and `TenPositiveTrace75.lean`; checks the row
difference from 76 listed above; checks that the body of `regsAt` is the
body of `TenPositiveTrace75.regs` with the `Y`, `X`, `s` lets removed and `W`
for `w` in `B`; parses `regsAt`, the q2 instance and structure update in
`regs`, and `value79`, and compares the output with the JSON output after
exact commutative-ring structural normalization (also `Y`, `D`, `Znum`,
`Mtot` individually). It rejects three mutations (denominator `q⁴`;
`Y = q³ s`; sign of the `q⁴ s` correction), checks the literal and endpoint
definitions verbatim, that `fixedPorts` is textually the `IPRATrace75` one,
and that the 79 `coefficient_binding` equals the 75 one, so
`reviews/bfs943-source-promotion/tools/check_ports.py` covers 79 too.
Output: `check-output.json`. These are finite external checks, not Lean
theorems about files.

## New modules (all in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `Trace79Regs` | `regsAt`, `regs75_eq`, 79 `regs`, `value79`, register lemmas |
| `Trace79Factors` | natural representatives (`Y = q² s`, `M = h q⁵ H`), `firstParam` |
| `Trace79Residue` | `c_eval`, signed residue |
| `Trace79NormRoots` | roots, adjacent Pell at an arbitrary carrier (q2) |
| `Trace79NormFold` | first/doubled Pell, indices, odd ordinate (q2) |
| `Trace79NormKpos` | first index `≥ 2`, radix size, `K > 0` (q2) |
| `Trace79NormRank` | rank window, auxiliary/main index, exact rank (q2) |
| `Trace79NormOffset` | first-index alignment, exact offset (q2) |
| `Trace79Transport` | `graph_bv_bound`, `graph_zero_data` |
| `Trace79ToTrace75` | positive 79 zero ⇒ positive 75 zero |
| `Trace79FromTrace76` | positive 76 zero ⇒ positive 79 zero |
| `Trace79Syntax` | literal `TenPositiveTrace79.expression`, `Trace79BFSSyntax.literal_zero_iff` |
| `Trace79ModelIff` | `positive_model_iff` |
| `IPRATrace79` | the iPRA endpoints |
