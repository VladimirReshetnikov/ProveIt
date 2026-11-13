# iPRA endpoints for package 163's ten-positive 76/352 circuit

Package 163 (`con-zfc-diophantine-forms/163-trace-radical`) supplies the
ten-positive circuit `compact/equations/trace76_degree352.json`: chart `q3`,
transport weight `L = bV` (`b = cT - R`), 76 operations, exact degree 352.
It differs from the already closed 75/402 circuit (`L = V²`) in one place:
the row `LBt = V2 * Bt` becomes `L = cTR * V; LBt = L * Bt`. Both graphs pin
the same four coefficient files (`coefficient_binding` is identical).

The Lean endpoints are in
`Lean/DiophantineConsistency/BFS943/IPRATrace76.lean`
(namespace `DiophantineConsistency.IPRATrace76`): `positiveBridge`,
`native_equivalence`, `standard_equivalence`, `reference_equivalence`,
`standard_translated_equivalence`, `reference_translated_equivalence`, at the
same direct-BFS943 ports `fixedPorts` as `IPRATrace75`. Each depends only on
`propext`, `Classical.choice`, `Quot.sound`.

## Route

**Soundness is a reduction to 75.** For every commutative ring,
`value76 p v = value75 p v'` where `v'` moves `n` to `n + (V² - bV) B`
(`TenPositiveTrace76.value75_update`, a ring identity). At a positive 76 zero
in a model of `𝗜𝚺₁`:

1. The root extraction, adjacent Pell descent, strong/auxiliary indices, odd
   ordinate, first index `≥ 2`, radix size and `K > 0` of the 75 chain never
   look inside the carrier `Z`. `TraceNormRoots`, `TraceNormFold` and
   `TraceNormKpos` restate them for `normValue (regs …) Z = 0` at an
   arbitrary carrier `Z` (same proofs). Both q3 circuits are instances
   (`value75_norm`, `value76_norm`, `rfl`).
2. `Trace76Estimate.bv_estimate` is the signed transport estimate for the
   `bV` weight: `2 g y < b V`, `0 ≤ b V`, `0 ≤ V² - b V`. It uses only the
   adjacent norm `(1+B) V0² = 1 + B y²` at `V0 = |V|` and `c < B`, `2c < F`,
   `8g ≤ F`, `F² + F ≤ 4B`: `b = 0` is excluded by the norm; for `b ≠ 0`,
   `V0 ≥ F - c > 1`, the norm gives `y ≥ V0 + 1`, hence `V0 > 2B`, and
   `y < 2V0`; so `F|b| ≥ V0 - c > 4gF`, i.e. `|b| > 4g`. This replaces
   PROOF.md §4's index-three exclusion (4.2): that exclusion is true but not
   needed, because already `V0 > 2B` follows from the norm.
3. `Trace76Transport.graph_transport`: `B ≥ 0` (the generic carrier
   contradiction at weight `bV`, with the offset bound `2e < bV·D` of
   `bv_offset`), hence `0 ≤ (V² - bV) B`.
4. `Trace76ToTrace75.positive75_of_positive76`: the moved point is a positive
   75 zero; `Trace75BFSModelHalt.graph_halts` (the promoted chain) gives a
   halting time of machine 215.

So no LeafFacts/FixedSource layer was needed for 76: the promoted 75 word
layer is reused through the zero transfer, not through a bundled interface.

**Completeness** is the 75 construction with the carrier coordinate chosen
for the new weight (PROOF.md §7, (7.2)). The §7.1 shift `T ↦ fT - dR`
multiplies `b` by `f` and keeps `V = oldV`, so the parent weight is
`f·b·oldV` (`Trace76ParentMap.oldZ76`, `value76_shift`), and
`Trace76ReverseData` picks `n + κ = τfy + (F b0 u)(βJ t) + t + ρ` with
`b0 = CT - R > 0` (from `F²CT = u + C + F²R`). `Trace76ReverseGraph`,
`Trace76PackingReverseGraph`, `Trace76HaltGraph` are the 75 files with these
replacements. A plain zero transfer 75 → 76 is not available (it would
lower `n` by `(V² - bV) B`), which is why completeness is re-derived.

## Binding check

`check_lean_graph.py` (run `py -I -X utf8 -B check_lean_graph.py`) pins the
76 and 75 JSON graphs and `TenPositiveTrace75.lean`, parses the 75 `regs`
and the body of `value76`, and compares the output with the JSON output
after exact commutative-ring structural normalization (also the `L` and
`Znum` rows individually). It checks the literal and endpoint definitions
verbatim, that `fixedPorts` is textually the `IPRATrace75` one, and that the
76 `coefficient_binding` equals the 75 one, so
`reviews/bfs943-source-promotion/tools/check_ports.py` (which binds the four
port integers to those hashes) covers 76 too. Output: `check-output.json`.
Three operator/operand mutations of `value76` (weight `V*V`, `L*b`, sign of
`Z²`) were each rejected. These are finite external checks, not Lean
theorems about files.

## New modules (all in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `Trace76Circuit` | `normValue`, `Z76`, `value76`, `value75_update` |
| `Trace76Syntax` | literal `TenPositiveTrace76.expression`, `Trace76BFSSyntax.literal_zero_iff` |
| `TraceNormRoots` | roots, `V ≠ 0`, adjacent Pell at an arbitrary carrier |
| `TraceNormFold` | first/doubled Pell, strong/auxiliary indices, odd ordinate |
| `TraceNormKpos` | first index `≥ 2`, radix size, `X < c`, `K > 0` |
| `Trace76Estimate` | `bv_estimate`, `bv_offset` (ordered rings) |
| `Trace76Transport` | `graph_bv_bound`, `graph_transport` |
| `Trace76ToTrace75` | positive 76 zero ⇒ positive 75 zero |
| `Trace76ReverseData` | `positive_carrier_weight`, `reverse_data` |
| `Trace76ParentMap` | parent at weight `f b oldV` and its positive map |
| `Trace76ReverseGraph` | source data ⇒ positive 76 zero |
| `Trace76PackingReverseGraph` | packing ⇒ positive 76 zero |
| `Trace76HaltGraph` | halting ⇒ positive 76 zero at the model ports |
| `Trace76ModelIff` | `positive_model_iff` |
| `IPRATrace76` | the iPRA endpoints |
