# Nine-positive point 82/726: iPRA endpoint

Target: package 82's `nine_full_radical/laurent9_positive.json` (nine positive unknowns
`b g h s w C i j n`, 726 live operations, exact degree 1,158,228, SHA-256 `56e8629e…`) on the
tree-calibrated wang943-mixed-121x8801 tuple (`Mixed121Ports.ports`). The endpoint has the usual
shape (`positiveBridge`, `native_equivalence`, `standard_equivalence`, `reference_equivalence`), as
for the 101/420, 105/456 and 101/1,057 points in `../nine-positive-p101-420-endpoint/`,
`../nine-positive-p105-456-endpoint/` and `../nine-positive-p101-1057-endpoint/`.

**Status: endpoint closed.** `IPRANine82p726` proves `positiveBridge` and the native, standard and equality-only iPRA equivalences for the Lean literal of the 726 equation at the wang943-mixed-121x8801 ports, with only `[propext, Classical.choice, Quot.sound]`. The literal is bound to the pinned JSON by `tools/check_graph.py`.

## What is new compared with 101 and 105

Three facts decide how much of the earlier routes carries over.

* **The source is the package-31 parent itself.** 82 keeps package 71's source65 prefix. Its
  shared-tap kernels (`65-shared-taps/nine/data/kernels.json`) record the source SHA-256
  `1c336ba0…`, which is `parent_source.json`, the package-31 parent of `Source31Rows`. The rows are
  the parent rows after the row operations `ρ₁₃ = r₁₃ + r₁`, `ρ₁₄ = r₁₄ + r₂` (0-based) with **no**
  coordinate map (the "unshifted transport source"); this is exactly `N101Source.transformed`. So
  the halting link is `Source31Facts.halts` / `Source31Converse.converse` unchanged, and the code
  coordinates are the parent coordinates minus one.
* **The layout is new.** The weights are 105's (`1 … 116`), but the targets (largest 1841), the
  shared-tap kernels (7 + 38 + 39 records, degrees 1384, 1739, 1641) and the height 1873 are
  source65's, so `N82Layout` carries its own `SparseCheck` certificate (22 pair checks, as in
  `N101Layout`). The prefix exponents are `N₀ = B¹¹⁷`, `L = bB¹⁹⁹¹`, `N = 2^17079501 bB¹⁰⁵⁷`,
  `t = bB¹¹⁶`; the population is `σ(T_c) = 139v − 31k − 22` and `2ν = u + σ(T_c)` for
  `u = k + 1991v`, `ν = 17079501 + k + 1057v`.
* **The finalizer has Jones's `F` and a full-radical Laurent majorant.** Package 71's Pell registers
  use Jones's `F = (A² − 1)E² + 1`, `E = iJC²D` (101 and 105 use `F = (A² − 1)D(iJC²)² + 1`) with the
  saturated `H = C + F(B₁ + (j − 1)C)`; `SatPellJ` is the matching sibling of `SatPell`. The
  majorant is `T = 4T₀(A, C, i, Z)` with `S = 2¹⁸C⁷`, `a₁ = DFI·S²`.

## The majorant in Lean (`N82Majorant`, `TopDom`)

The package certifies `Δ₀ = T₀² − 2³²C¹⁴DFI > 0` by its translate under `A = x + 3, C = y + 1,
i = z + 1, t = u + 3` (32,637 positive coefficients). Lean does not use that table. Instead:

* three Kronecker identity checks (`Kron.kcheckK`, one `decide +kernel` each): the graph's evaluator
  `T = 64C⁷H(T₇ − 640i − 4096) − Corr` equals `4T₀` (box `24 × 32 × 6 × 2`, `X = 2⁴⁹`);
  `T₀² − 2³²C¹⁴DFI = A²²t²P + rest` (box `47 × 63 × 11 × 3`, `X = 2⁹¹`), where `P` are the 19 terms of
  `Δ₀` at `A²²t²` and `rest` the other 3,762; `P − κC⁴²i¹⁰ = Q(C − 1, i − 1)` with
  `κ = 141664530202624` (the leading coefficient of `Δ₀`) and `Q` a Horner form with 473
  nonnegative coefficients (box `1 × 43 × 11 × 1`, `X = 2¹³⁰`);
* `TopDom.pos_split`: every term of `rest` divides `A²²C⁴²i¹⁰t²`, its negative coefficients sit at
  `A`-degree `< 22` or `t`-degree `< 2`, and `κ·2²⁰ + ν > 0` (`ν ≈ −7.0·10¹⁹`); so `Δ₀ > 0` for
  `A, t ≥ 2²⁰`, `C, i ≥ 1`. `TopDom.NN_nonneg` gives `Q ≥ 0`;
* `T₀ > 0` by `SP4.pos_of_check` (top `A²³C³¹i⁵t`, `κ = 2²⁶`);
* `T > AD` follows from `S²DFI ≥ DF ≥ A²D²`.

The prefix guarantees the hypotheses: `R ≥ 2²⁰` (from `L ≥ B²`), `N ≥ 32`, hence `A ≥ 2²⁰` and
`Z = 2R + 1 + (j − 1)C ≥ 2²⁰` (`N82Contract.prefix_naturals`).

## Route

```
nine-variable zero (b g h s w C i j n > 0)
  ──[N82Finalizer.sound: 0 < T, S²DFI < T², T > AD (N82Majorant.majorant), m > 0, roots,
     S ∣ √a₁, SatPellJ.psi_of_satJ, Lemma 2.25]──▶ N² ∣ C(2R,R), b = 2ᵏ, g < 4t   (prefix R, N, t)
  ──[N82Contract.contract: SparseCentral + SignedDigits + low mask]──▶
      g = Σ zᵢ B^{wᵢ}, zᵢ < b, transformed parent rows(z + 1) = 0          (N82Layout.coeff_target)
  ──[N82Contract.source_of_code]──▶ positive parent zero ──[Source31Facts.halts]──▶ machine 215 halts
converse:
  halt ──[Source31Converse.converse]──▶ parent zero ──[N82Contract.code_of_source]──▶ code g < t, b = 2ᵏ
       ──[contract]──▶ N² ∣ C(2R,R) ──[N82Finalizer.complete, SatPellJ.exists_satJ]──▶ nine-variable zero
```

## Modules (`Lean/DiophantineConsistency/Nine121/`)

Reused unchanged: `Source31Rows/Facts/Converse`, `N101Source` (`transformed`), `N101Prefix` (`Bq`,
`baseScale`, generic order lemmas), `N101Contract` (port bounds, scales, `Bm`, `v_facts`), `N9Norm`,
`N9Finalizer` (`Q.*`, `S.D`, `S.r`, `marg`, `Qr`, `a0`, `V0`, `register_sizes`), `SparseCheck`,
`SparseExtraction`, `SparseCentral`, `SignedDigits`, `LowMask`, `DigitPopulation`, `SparsePoly4`,
`Kron4`. Nothing in the committed modules was changed.

| Module | Content | Build |
|---|---|---|
| `N82Layout` | generated (`tools/generate_n82_layout.py`): weights, row-ordered targets, the 7+38+39 shared-tap kernel records with port-polynomial coefficients, index lists `S2/S1/S0` (74+39+7 interactions), `SparseCheck` certificate (22 pair checks); `transformed_zero_iff`; `coeff_target : [T^{q_k}](K₂U² + K₁U + K₀) = 2ρ_k` for `N101Source.transformed` | built, clean axioms (about 5 min, peak about 3.1 GB) |
| `N82Prefix` | the source65 prefix in any commutative ring (`thresholdScale82 = 2^17079501` irreducible; `ell`, `Tst`, `ker0/1/2`, `Ust`, `Gs`, `N0`, `maskq`, `Tcq`, `Scq`, `Lq`, `Rq`, `Nq`, `tq`); `Gs_sum` (`natDegree ≤ 1873`); `c_bounds` (84 coefficients); `Gs_pos`, `Gs_le`, `coeff_bound`, `sum_lt_L` | built (about 4 min, peak about 2.6 GB) |
| `N82Contract` | at `Mixed121Ports.ports`: `port_facts`; `prefix_naturals` (also `R ≥ 2²⁰`, `N ≥ 32`); `high_iff`; `pop_low`/`pop_high`; `contract`: for `b = 2ᵏ`, `g < 4t`, `N² ∣ C(2R,R) ↔ ∃ z < b, g = Σ zᵢB^{wᵢ} ∧ ρ(z+1) = 0`; `source_of_code`, `code_of_source` (positive `g < bB¹¹⁶`) | built, clean axioms (about 5.5 min, peak about 3.0 GB) |
| `SatPellJ` | derived from `SatPell` (Jones's `F`, saturated `H`): `psi_of_satJ` (soundness), `exists_satJ` (completeness, Jones's own `i`) | built, clean axioms (about 30 s, peak about 2.5 GB) |
| `TopDom` | handwritten, generic: `restOk`, `negAll`, `pos_split` (positivity by a dominating top group at `a^{e₀}z^{e₃}`); `NN`, `NN_nonneg` (sums/products of nonnegative literals and `x − 1`) | built (about 20 s) |
| `N82Majorant` | generated (`tools/generate_n82_majorant.py`): `tBlock` (JSON cone of node 844, 418 lets), `TR`; `Dr Er Fr Gr Hr Ir Sr`; `T0T` (654), `PT` (19), `restT` (3,762), `Qrow0…10`, `QhZ`; `idT_check`, `idD_check`, `idQ_check` (Kronecker), `T0_check`, `rest_check`, `rest_neg`, `Q_check`; `T_eq`, `defect_eq`, `P_eq`; `majorant` | built, clean axioms (`majorant`; about 1 min, peak about 3.4 GB) |
| `N82Finalizer` | sibling of `N1057Finalizer` (reuses `Q.*`, `S.D`, `S.r`, `marg`, `Qr`, `a0`, `V0`, `register_sizes`): `value`, registers `S82.E/F/G/H/I`, `sc`, `a1`, `Zr`, `V1`; `A_big`, `big_Zr`; `value_eq`; `sound`, `complete` (hypotheses `N ≥ 32`, `R ≥ 2²⁰`) | built, clean axioms (about 13 min, peak about 2.9 GB) |
| `N82p726Graph` | generated (`tools/generate_n82p726_graph.py`): one `def` per JSON node; closed forms `eᵢ`, prefix registers `sᵢ`, 26 finalizer registers `rᵢ` (`r844 : T = N82Majorant.TR A C i Z` by unfolding the cone and `rfl`); `value_regs`; `output_eval : eval = N82Finalizer.value (Rq) (Nq) b g (tq) h s w C i j n` | built, clean axioms (`output_eval`; about 2.5 min, peak about 3.9 GB) |
| `IPRANine82p726` | `expression` (node 860 at the ports), `expression_def`, `forward`, `backward`, `positiveBridge`, `native_equivalence`, `standard_equivalence`, `reference_equivalence` | built: all four endpoint theorems `[propext, Classical.choice, Quot.sound]` (about 4 min, peak about 3.5 GB) |

## Checkers

* `tools/generate_n82_layout.py --check`, `tools/generate_n82_majorant.py --check`,
  `tools/generate_n82p726_graph.py --check`: byte-identical regeneration. The layout generator
  re-derives the 22 extraction identities from the parent rows; the majorant generator checks, as
  exact polynomial identities, `block = 4T₀`, the radicand and `Δ₀` against
  `laurent_candidate.json`, the three Lean identities, `Q ≥ 0`, both domination conditions, the
  Kronecker boxes and bounds (and the Kronecker equality modulo `2¹²⁷ − 1`), and the package's
  translated cone certificate (9,216 + 32,637 positive coefficients, used only here).
* `tools/check_binding.py` → `CHECK.json`: `N82Layout.lean` and `N82Majorant.lean` regenerated byte for
  byte; `Source31Rows.rows` parses to the 22 parent equations; 82's four raw coefficient SHA-256
  values (`COEFFICIENT_RECONSTRUCTION.json`, instance wang943-mixed-121x8801) equal package 55's
  wang943-mixed-121x8801 payloads; the JSON source parameters and the `N82Prefix` exponents agree;
  five mutations are rejected (kernel coefficient, weight, target, parent-row coefficient, port hash).
* `tools/check_graph.py` → `CHECK_GRAPH.json`: `N82p726Graph.lean` regenerated byte for byte (the
  generator first checks every closed form, every register formula and output = `value(prefix)` on
  the JSON DAG modulo `2¹²⁷ − 1` at random points, with `T` evaluated independently as `4T₀`); every
  `def nᵢ` parsed back and compared gate by gate with the pinned JSON; the endpoint expression; the
  `tBlock` lets parsed back and compared with the JSON cone of node 844; ten mutations rejected.

## Axioms

Every built theorem prints `[propext, Classical.choice, Quot.sound]`: `N82Layout.coeff_target`, `N82Contract.prefix_naturals/contract/code_of_source`, `SatPellJ.psi_of_satJ/exists_satJ`, `N82Majorant.majorant`, `N82Finalizer.value_eq/sound/complete`, `N82p726Graph.output_eval`, and `IPRANine82p726.positiveBridge/native_equivalence/standard_equivalence/reference_equivalence`.

There is no `sorry`, `native_decide`, `axiom`, `unsafe`, `implemented_by` or `maxHeartbeats 0`.
The kernel checks are `decide +kernel`. Finite heartbeat raises are used (up to `8000000`).

## Scope and non-claims

* What is shown: in native, standard and equality-only iPRA, *no natural zero of
  `positiveShift IPRANine82p726.expression`* ↔ *Con(ZFC)* for the selected Foundation ZFC
  consistency predicate. Here `expression` is the Lean literal `N82p726Graph.n860` at
  `Mixed121Ports.ports`.
* The JSON ↔ literal correspondence (`check_graph.py`), and that of the ports, the source65 layout
  and the majorant data with the package files (`check_binding.py`), is a finite external check, not
  a Lean theorem. This is not a paired replay.
* The ports are package 55's 121x8801 payloads; package 82's own payload files are not in the tree,
  only the raw SHA-256 values of its coefficient reconstruction are compared.
* Lean does not use the package's 32,637-term translated certificate; it certifies `Δ₀ > 0` by
  domination for `A, t ≥ 2²⁰`, which the prefix guarantees. The equality of the translate with the
  package certificate is checked only by the generator.
* The exact degree 1,158,228 and the operation count are package claims; the checker counts the 726
  operations but the degree is not re-proved here. Package 71's 478-operation form is not covered.

## What remains

Nothing for the 726 endpoint itself. Build times above were measured on a memory-constrained machine and vary with memory pressure.
