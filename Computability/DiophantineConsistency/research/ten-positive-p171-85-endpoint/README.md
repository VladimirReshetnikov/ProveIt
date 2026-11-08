# iPRA endpoints for the ten-positive 85/232 scaled inverse-Lucas circuit

Package 171 (`con-zfc-diophantine-forms/171-pooled-powers-separated-radicals`)
supplies `positive/equation_bV.json` (85 operations, exact degree 232, weight
`L = bV`; proof: `positive/PROOF.md`). Package 172's
`part2/ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/positive10/positive10_degree232_ops85.json`
(mode `scaled_inverse`) is the same polynomial: its `source` rows and all
polynomial metadata are equal, and both port bindings are the direct-BFS943
tuple (checked by `check_lean_graph.py`), so one endpoint covers both. The
`positive/one_anchor7309/` copy is another tuple and is not covered.

In the notation of package 171's proof, with `h = β J`, `q = h + 1`,
`C = q - F - α`, `k = η + ζ`:

* `X = q w`, `Y = q s`, the scaled strip `c = k Y + η`, the Pell base
  `A = Y (X + 1) + 1` and the first parameter `v = X Y²`, transport base `w`;
* `D = 6 q⁶` and the inverse-Lucas offset
  `eclear = 6 (e - q⁴ s) - v k (k² - 4)` with `e = k - R - 1`;
* `B = (K0 + w) C - F`, `V = f (c T - R) - c`, `L = b V`,
  `Z = h D [H (n - L B) + K] - H [D B + h eclear]`, `M = h D H`.

It differs from package 172's 87/214 circuit (`research/ten-positive-p172-87-endpoint`)
in exactly two places: the strip is the scaled one `c = k Y + η` (87: free,
`c = k s + η`) and the denominator is `6 q⁶` (87: `6 q⁷`). The Lean register
map is `TenPositiveTrace79.regsAt p v (q w) (q s) w` (whose strip is
`c = k Y + η`) with `D`, `Z`, `M` replaced.

The `coefficient_binding` equals the 75/402 graph's in every port field except
the relative `path` (171 also carries `endianness: little`): K0 raw
`0a86821a…`, MC `6007cabd…`, MF `48333b0d…`, β `0664a868…`.

The Lean endpoints are in `Lean/DiophantineConsistency/BFS943/IPRATrace85.lean`
(namespace `DiophantineConsistency.IPRATrace85`): `positiveBridge`,
`native_equivalence`, `standard_equivalence`, `reference_equivalence`,
`standard_translated_equivalence`, `reference_translated_equivalence`, at the
same ports `fixedPorts` as `IPRATrace75`. Each depends only on `propext`,
`Classical.choice`, `Quot.sound`.

## Route

The chain is the 87 chain with the 80 strip. The norm layer
(`Trace85Factors` … `Trace85GraphPower`) was produced as a three-way merge of
`Trace87*` (`X = q w`, the literal `6`, the inverse-Lucas offset) and
`Trace80*` (the scaled strip, `q⁶`) over the common ancestor `Trace82*`,
with the conflicts resolved by hand.

**Soundness** (package 171 §§2–4). `Trace85Transport`: `B ≥ 0` by the carrier
contradiction with `2 eclear ≤ 12 (e - q⁴ s) < bV D`; at the first index
`eclear = 6 u`, the carrier gives `6 q⁶ ∣ h H (6 u)`, so `q⁶ ∣ u`; with
`q⁶ ∣ v²` and `InverseLucasCubic.cancel_three`, `q⁴ ∣ 2n - R - 1`, hence
`2n = R + 1` (`Trace85NormOffset`). `Trace85Projection`: `H ∣ 6 h K` (six
cancellations of `q`), then `X = 2^R` (`Trace85GraphPower`, with
`Trace87ProductPower`) and `H ∣ K` (`Trace85Unweighted`).
`Trace85Integral`: `3 u = q⁴ s (X² s³ w - 3)` and `q⁶ ∣ u` give
`q² ∣ s (X² s³ w - 3)`, so `q² ∣ s` (`pow2_cancel_signed_odd`), i.e. `q³ ∣ Y`;
and `h ∣ B`, the natural transport. `Trace85Sandwich`: both scaled Pell
sandwiches with strip ordinate `Y` (`c < k (Y + 1)`). `Trace85Source`: a
positive 85 zero is a `BFS943FixedSource.FixedSource` at
`![J, F, α, 1, 1, w, 1, 1, 1, 1]`, the population bound coming from
`2 Y = C(2r, r) + z X` and `2^{3ℓ} ∣ Y`.

**Completeness** (package 171 §5). `Trace85HaltGraph`: the packing's seed
ordinate `s_Y q³` is the 85 register `Y`, so `s = s_Y q²`, and the transport
base `2^{R - uN}` is `w`. `Trace85ReverseData`: `scaled_start` at scale `1`
(as in `Trace76ReverseData`) gives fresh data at the Pell base `Y (X + 1) - 1`
with the scaled strip `C = K Y + η'`; the inverse-Lucas split at the first
index gives `eclear = 6 u` with `3 (u + q³ Y) = P² w`, `q¹² ∣ P²`, so
`u = q⁶ ρ` (`cancel_three`), `ρ` integral but possibly negative, with
`-ρ ≤ q³ Y + P K³ < f`; the carrier coordinate
`n = τ f y + (1 + b L) t + ρ - κ` is positive. `Trace85ParentMap` (copy of
`Trace87ParentMap`) and `Trace85ReverseGraph` give the positive 85 zero.

`Trace85ModelIff.positive_model_iff` joins both directions; the iPRA wrappers
are those of `IPRATrace75`.

## Binding check

`check_lean_graph.py` (run `py -I -X utf8 -B check_lean_graph.py`) pins both
85 JSON files, the 75 JSON graph, the 87 record's checker (whose parser and
normalizer it imports), `TenPositiveTrace75.lean` and `Trace79Regs.lean`;
checks that the 171 and 172 files are one polynomial on one tuple; checks the
graph metadata, no dead rows, the port bindings with the four direct-BFS943
raw hashes, and that `regsAt` is the parameterized 75 register map; parses
`regsAt`, the 85 instance, lets and structure update in `regs`, and
`value85`, and compares with the JSON output after exact commutative-ring
structural normalization (also `X`, `Y`, `c`, `Bt`, `sixq6`, `eclear`,
`Znum`, `Mtot`). It rejects seven mutations (denominator `6 q⁷`, denominator
without `6`, chart `X = q (q w)`, Pell scale `1`, transport base `q w`, sign
of the `q⁴ s` correction, sign of the inverse cubic), and checks the literal
and endpoint definitions verbatim and that `fixedPorts` is textually the
`IPRATrace75` one, so `reviews/bfs943-source-promotion/tools/check_ports.py`
covers this circuit. Output: `check-output.json`. Finite external checks, not
Lean theorems about files.

## New modules (all in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `Trace85Regs` | `regs`, `ecl`, `value85`, register lemmas |
| `Trace85Factors` | natural representatives (`X = q w`, `c = k Y + η`, `D6 = 6 q⁶`) |
| `Trace85Residue` … `Trace85NormKpos` | norm layer |
| `Trace85NormRank` | rank window, main index, `two_q4_lt_c` |
| `Trace85NormOffset` | first-index alignment from the residue hypothesis |
| `Trace85Transport` | `B ≥ 0`, mask, `eclear = 6 u`, `q⁶ ∣ u`, `q⁴ ∣ 2n - R - 1` |
| `Trace85Projection` | `H ∣ 6 h K`, whole-product projection, `zero_alignment` |
| `Trace85VariableHeight`, `Trace85GraphPower` | `X = 2^R` |
| `Trace85Unweighted` | `H ∣ K` |
| `Trace85Integral` | `q² ∣ s`, natural transport `(K0 + w) C = F + h t` |
| `Trace85Sandwich` | both scaled Pell sandwiches at the scaled strip |
| `Trace85Source` | positive 85 zero ⇒ `FixedSource` |
| `Trace85ParentMap` | squared-trace parent and its positive shift |
| `Trace85ReverseData` | reverse data at scale `1` with the signed inverse offset |
| `Trace85ReverseGraph` | source data ⇒ positive 85 zero |
| `Trace85HaltGraph` | halting ⇒ positive 85 zero |
| `Trace85Syntax` | literal `TenPositiveTrace85.expression`, `Trace85BFSSyntax.literal_zero_iff` |
| `Trace85ModelIff` | `positive_model_iff` |
| `IPRATrace85` | the iPRA endpoints |
