# iPRA endpoints for package 171's ten-positive 77/348 circuit

Package 171 (`con-zfc-diophantine-forms/171-pooled-powers-separated-radicals`)
supplies the ten-positive circuit `positive/q4_interpolation/equation.json`:
chart `q4`, transport weight `L = bV`, 77 operations, exact degree 348. Its
own proof is `positive/q4_interpolation/PROOF.md`. It differs from package
163's 76/352 circuit in one place: a new row `q4 = q2 * q2`, used instead of
`XY` as the denominator `D` in `P1mu2 = bJ * D` and `mu2inner = D * Bt`
(`XY` stays, for `Am1` and `V0k`). So `D = q⁴`, `M = h q⁴ H` and

  `Z = h q⁴ [H (n - bV B) + K] - H [q⁴ B + h e]`.

The `coefficient_binding` names the same four files, bit lengths, raw and
gzip SHA-256 and tuple as the 75/402 graph (only the relative `path` and an
added `endianness: little` differ): this is the direct-BFS943 tuple (K0 raw
`0a86821a…`, MC `6007cabd…`, MF `48333b0d…`, β `0664a868…`).

The Lean endpoints are in
`Lean/DiophantineConsistency/BFS943/IPRATrace77.lean`
(namespace `DiophantineConsistency.IPRATrace77`): `positiveBridge`,
`native_equivalence`, `standard_equivalence`, `reference_equivalence`,
`standard_translated_equivalence`, `reference_translated_equivalence`, at the
same direct-BFS943 ports `fixedPorts` as `IPRATrace75`. Each depends only on
`propext`, `Classical.choice`, `Quot.sound`.

## Route

**The scaling identity.** `XY = (w s) q⁴`, so the 75 multiplier is `w s`
times the 77 one, and for every commutative ring
(`TenPositiveTrace77.norm_scaled`)

  `normValue (regs p v) (w s Z77) = (w s)² value77`.

Thus a 77 zero is a zero of the 75/76 norm at the carrier `w s Z77`, which
is the 76 carrier with offset `w s e` in place of `e` (`scaled_shape`). All
carrier-free facts of `TraceNormRoots`, `TraceNormFold`, `TraceNormKpos`
apply unchanged.

**Soundness is a zero map to 75**, but not a pure ring identity in `n`: the
carriers differ by `(w s - 1) e / XY`, which is integral only after the
first-index alignment.

1. `Trace77Transport.graph_zero_data`: `w s Z77 = M z` with `z = ±τ f y`;
   `B ≥ 0` by the generic carrier contradiction at weight `bV` and
   denominator `q⁴` (offset bound from `Trace76Estimate.bv_offset`); the mask
   `F + α < q`; and `q⁴ ∣ e` (reduce `Z77 = h q⁴ H z` mod `q⁴`, `hH ≡ 1 mod q`).
2. `TraceNormRank`, `TraceNormOffset` (new, reusable): the 75 rank window,
   rank auxiliary index, main index, exact rank, first-index residue,
   index alignment and exact offset, restated at an arbitrary carrier `Z`
   with the mask and `q⁴ ∣ e` as explicit hypotheses. They give
   `e = 4 X Y² s`, i.e. `e = XY ρ` with `ρ = 4 Y s ≥ 0`.
3. `Trace77ToTrace75.positive75_of_positive77`: with `g = τ f y = |z|`, the
   moved coordinate `n' = n + (V² - bV) B - (w s - 1) ρ + (g - z)` makes the
   75 carrier `M g` (`Z75_shift`), whose square is that of `w s Z77`, so the
   75 output vanishes. Positivity: `h H n' = h H g + h H V² B + H B + h H ρ - h K`
   and `H g > K` since `g ≥ f > c` (`f² = 1 + a ≥ 1 + c²`) and `H ≥ 4X + 3`.
   Using `|z|` instead of `z` is what avoids any sign case on the carrier.
4. `Trace75BFSModelHalt.graph_halts` (the promoted chain) gives a halting
   time of machine 215.

**Completeness is a zero map from 76** (`Trace77FromTrace76`): halting gives
a positive 76 zero (`Trace76HaltGraph`); moving its `n` by `(V² - bV) B ≥ 0`
gives a positive 75 zero with the same `e`, so the promoted
`Trace75OffsetExact.graph_offset_exact` gives `e = XY ρ`, `ρ ≥ 0`; then
`n + (w s - 1) ρ` is a positive 77 zero (`value77_shift`:
`(w s)² value77(n + (w s - 1) ρ) = value76(n)`). No 77-specific reverse
construction was needed.

The reusable layer for further q3-type charts is `TraceNormRank` +
`TraceNormOffset` (with the earlier `TraceNorm*` modules): any circuit whose
output is, up to a nonzero factor, `normValue (regs p v) Z` for the q3
register map needs only its own mask and `q⁴ ∣ e` to reach `e = 4XY² s`.

## Binding check

`check_lean_graph.py` (run `py -I -X utf8 -B check_lean_graph.py`) pins the
77, 75 and 76 JSON graphs and `TenPositiveTrace75.lean`; checks that the 77
rows are exactly the 76 rows plus `q4 = q2 * q2` with `P1mu2`, `mu2inner`
reading `q4` for `XY`; parses the 75 `regs` and the body of `value77`, and
compares the output with the JSON output after exact commutative-ring
structural normalization (also `L`, `q4`, `Znum`, `Mtot` individually). It
rejects three mutations of `value77` (denominator `q³`; multiplier with the
75 denominator `XY`; sign of the offset term), checks the literal and
endpoint definitions verbatim, that `fixedPorts` is textually the
`IPRATrace75` one, and the port binding described above, so
`reviews/bfs943-source-promotion/tools/check_ports.py` covers 77 too.
Output: `check-output.json`. These are finite external checks, not Lean
theorems about files.

## New modules (all in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `Trace77Circuit` | `Z77`, `M77`, `value77`; `norm_scaled`, `scaled_shape`, `Z75_shift`, `value75_of_carrier_sq`, `value77_shift` |
| `TraceNormRank` | rank window, auxiliary/main index, exact rank at an arbitrary carrier (mask as hypothesis) |
| `TraceNormOffset` | offset congruence, first-index residue, alignment, exact offset (mask, `q⁴ ∣ e` as hypotheses) |
| `Trace77Transport` | `graph_bv_bound` (with `τ, f, y`), `graph_zero_data` |
| `Trace77ToTrace75` | positive 77 zero ⇒ positive 75 zero |
| `Trace77FromTrace76` | positive 76 zero ⇒ positive 77 zero |
| `Trace77Syntax` | literal `TenPositiveTrace77.expression`, `Trace77BFSSyntax.literal_zero_iff` |
| `Trace77ModelIff` | `positive_model_iff` |
| `IPRATrace77` | the iPRA endpoints |
