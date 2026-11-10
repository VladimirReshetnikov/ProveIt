# Nine-positive point 105/456: iPRA endpoint

Target: package 105's `nine/equations/h1868.json` (nine positive unknowns `b g h s w c i j n`,
456 live operations, exact degree 1,376,378, SHA-256 `9c3d4b0b…`) on the tree-calibrated
wang943-mixed-121x8801 tuple (`Mixed121Ports.ports`). The endpoint has the usual shape
(`positiveBridge`, `native_equivalence`, `standard_equivalence`, `reference_equivalence`), as for
the 101/420 point in `../nine-positive-p101-420-endpoint/`.

**Status: endpoint closed.** `IPRANine105p456` proves `positiveBridge` and the native, standard and equality-only iPRA equivalences for the Lean literal of the 456 equation at the wang943-mixed-121x8801 ports, with only `[propext, Classical.choice, Quot.sound]`. The literal is bound to the pinned JSON by `tools/check_graph.py`.

## What is new compared with 101/420

Two facts decide how much of the 101/420 route carries over.

* **The layout is 101's, untranslated.** 105's H1868 tables (`nine/source/h1868/`) are package
  101's translated original31 tables shifted back: weights +1 (1..116), targets +2 (max 1836), kernel
  positions +2 / +1 / +0 for the constant / linear / quadratic kernel, with identical
  port-polynomial coefficients over the same gapN86 rows. Hence
  `N105Layout.sourcePoly = X² · N101Layout.sourcePoly`, and the extraction identity follows from
  `N101Layout.coeff_target` with no second sparse certificate (`N105Layout` builds in about 4 min,
  compared with the 22 pair checks of `N101Layout`).
* **The finalizer is not 101's.** 105 replaces the simple majorant `V₁ = ADrGH`, `a₁ = DFI` of
  `N9Finalizer.value` by the local Laurent majorant `T = iC²(AJ(2D − C²) + 3C² − 4)`, `V₁ = TGH`,
  `a₁ = 4DFI`, at the successor coordinate `C = c + 1`. `N105Finalizer` is a sibling of
  `N9Finalizer` (it imports it and reuses its saturated registers `S.*`, `marg`, `Qr`, `a0`, `V0`
  and `register_sizes`). Nothing in the 101/420 modules was changed.

The prefix differs only in its exponents: `N₀ = B¹¹⁷`, `L = 2bB¹⁹⁸⁶`, `N = 2^16012032 B¹⁰⁵⁵`,
`t = bB¹¹⁶`, height 1868. The base `B = 2^2134939 b²`, the two irreducible scales and the 81 kernel
coefficients are 101's.

## Route

```
nine-variable zero (b g h s w c i j n > 0), C = c + 1 ≥ 2
  ──[N105Finalizer.sound_succ]──▶ N² ∣ C(2R,R), b = 2ᵏ, g < 4t          (prefix R, N, t)
  ──[N105Contract.contract: SparseCentral + SignedDigits + low mask]──▶
      g = Σ zᵢ B^{wᵢ}, zᵢ < b, gapN86 rows(z + 1) = 0                   (N105Layout.coeff_target)
  ──[N101Contract.source_of_code: N101Source.zero_iff, affine map]──▶ positive parent zero
  ──[Source31Facts.halts]──▶ machine 215 halts
converse:
  halt ──[Source31Converse.converse]──▶ parent zero ──[N105Contract.code_of_source]──▶ code g < t, b = 2ᵏ
       ──[contract]──▶ N² ∣ C(2R,R) ──[N105Finalizer.complete_succ]──▶ nine-variable zero (c = C − 1 > 0)
```

## Modules (`Lean/DiophantineConsistency/Nine121/`)

New modules (reused unchanged: `Source31Rows/Facts/Converse`, `N101Source`, `N101Layout`,
`N101Prefix` (scales, `Bq`, `c_bounds`, generic order lemmas), `N101Contract` (port bounds, `Bm`,
`v_facts`, `source_of_code`, the digit part of `code_of_source`), `N9Norm`, `N9Finalizer`,
`SatPell`, `SparseCentral`, `SignedDigits`, `LowMask`, `DigitPopulation`, `SparseExtraction`):

| Module | Content | Build |
|---|---|---|
| `N105Layout` | generated (`tools/generate_n105_layout.py`): the H1868 tables; `weights_shift`, `targets_shift`, `pos0/1/2_shift` (by `decide`); injectivity and bounds; `sourcePoly_shift : sourcePoly = X² · N101Layout.sourcePoly`; `coeff_target : [T^{q_k}](K₂U² + K₁U + K₀) = 2ρ_k` | built, clean axioms (about 4 min, peak about 2.3 GB) |
| `N105Prefix` | the prefix of PROOF.md §2 in any commutative ring (`ell`, `Tst`, `ker0/1/2`, `Ust`, `Gs`, `N0`, `maskq`, `Tcq`, `Scq`, `Lq`, `Rq`, `Nq`, `tq`); `Gs_sum` (`natDegree ≤ 1868`); `Gs_pos` (unconditional `G* > 0` from `U* ≥ B¹¹⁶`), `Gs_le`, `coeff_bound`, `sum_lt_L` | built (about 3 min, peak about 2.4 GB) |
| `N105Contract` | at `Mixed121Ports.ports`: `prefix_naturals`; `high_iff`; `pop_low`/`pop_high` (`σ(T_c) = 139v − 31k − 22`); `contract`: for `b = 2ᵏ`, `g < 4t`, `N² ∣ C(2R,R) ↔ ∃ z < b, g = Σ zᵢB^{wᵢ} ∧ ρ(z+1) = 0`; `code_of_source` (positive `g < bB¹¹⁶`) | built, clean axioms (about 5 min, peak about 3.0 GB) |
| `N105Finalizer` | the literal local Laurent finalizer `value`; `Qpos`, `majorant` (`T > 0`, `4DF < T²` for `A, C ≥ 2`, `i ≥ 1`); `value_eq`; `sound` (needs `C ≥ 2`); `complete` (gives `C ≥ 2`, uses `T ≥ AD`); `sound_succ`, `complete_succ` at `C = c + 1` | built, clean axioms (about 13 min, peak about 2.8 GB) |
| `N105p456Graph` | generated (`tools/generate_n105p456_graph.py`): one `def` per JSON node, gate-local evaluation lemmas (closed forms in `Bq b`, prefix registers, 25 finalizer registers including `r395 : C = c + 1`), `value_regs`, `output_eval : eval = N105Finalizer.value (Rq) (Nq) b g (tq) h s w (c + 1) i j n` | built, clean axioms (`output_eval`; about 3 min, peak about 3.7 GB) |
| `IPRANine105p456` | `expression` (node 487 at the ports), `expression_def`, `forward`, `backward`, `positiveBridge`, `native_equivalence`, `standard_equivalence`, `reference_equivalence` | built: all four endpoint theorems `[propext, Classical.choice, Quot.sound]` (about 2.5 min, peak about 3.5 GB) |

## The new majorant in Lean

`N105Finalizer.majorant` follows PROOF.md §4 literally: with `t = C²`,
`T² − 4DF = i²t²Q(A, t) − 4D` (`ring`), `Q(x + 2, y + 4) − (x + 2)²` is the explicit twelve-term
polynomial with positive coefficients (`Qpos`), so `T² − 4DF ≥ t²A² − 4D = A²t(t − 4) + 4t − 4 ≥ 12`.
Then `(TGH)² − 4DFI = (T² − 4DF)G²H² + 4DF(H² − 1) > 0`. In `sound`, after the roots
`z₀² = a₀`, `z₁² = 4DFI` are extracted, `ModelRelationCombining.sq_dvd_sq` gives `2 ∣ z₁`, so
`DFI` is the square needed by `SatPell.psi_of_sat`. In `complete`, the root is `2z₁` and
`n = m(V₀ + V₁ + z₀ + 2z₁) − W² − Q/J > 0` because `V₁ ≥ T ≥ AD > W² + Q`.

## Checkers

* `tools/generate_n105_layout.py --check`, `tools/generate_n105p456_graph.py --check`: byte-identical
  regeneration.
* `tools/check_binding.py` → `CHECK.json`: `N105Layout.lean` regenerated byte for byte (the generator
  re-derives the gapN86 rows from the package-31 parent through 101's generator, checks the shift
  relation exactly, and re-derives the 22 extraction identities directly for 105's own tables);
  `Source31Rows.rows` parses to the 22 parent equations; 105's four port SHA-256 values
  (`fixed/h1868/BINDING.json`) equal package 55's wang943-mixed-121x8801 payloads; the prefix
  constants of `N105Prefix` match `source_parameters`; five mutations are rejected (kernel
  coefficient, weight, target, parent-row coefficient, port hash).
* `tools/check_graph.py` → `CHECK_GRAPH.json`: `N105p456Graph.lean` regenerated byte for byte (the
  generator first checks every closed form, every register formula and output = value(prefix,
  `C = c + 1`) on the JSON DAG modulo 2^127 − 1 at random points); every `def nᵢ` parsed back and
  compared gate by gate with the pinned JSON; the endpoint expression; eight mutations rejected
  (child, operation, literal, variable, coefficient recipe, scale, a JSON literal and the literal
  3 of the majorant gate, each of the last two changing the output).

## Axioms

Every built theorem prints `[propext, Classical.choice, Quot.sound]`: `N105Layout.coeff_target`, `N105Contract.prefix_naturals/contract/code_of_source`, `N105Finalizer.majorant/value_eq/sound_succ/complete_succ`, `N105p456Graph.output_eval`, and `IPRANine105p456.positiveBridge/native_equivalence/standard_equivalence/reference_equivalence`.

There is no `sorry`, `native_decide`, `axiom` or `maxHeartbeats 0`. Finite heartbeat raises are
used: up to `8000000` in the finalizer, `4000000` elsewhere.

## Scope and non-claims

* What is shown: in native, standard and equality-only iPRA, *no natural zero of
  `positiveShift IPRANine105p456.expression`* ↔ *Con(ZFC)* for the selected Foundation ZFC
  consistency predicate. Here `expression` is the Lean literal `N105p456Graph.n487` at
  `Mixed121Ports.ports`.
* The correspondence of that literal with the JSON circuit (`check_graph.py`), and of the ports and
  the H1868 tables with package 105's files (`check_binding.py`), is a finite external check, not a
  Lean theorem. This is not an independent paired replay.
* The ports are 101's original31 tuple (package 55's 121x8801 payloads). 105's own
  `ports/h1868/` payload files are not in the tree; only their SHA-256 values in `BINDING.json`
  are compared.
* The exact degree 1,376,378 and the operation count are package claims; the checker counts the
  456 operations but the degree is not re-proved here.
* 105's other circuit, `compact2082.json` (442 / 1,520,186), is on the compact54-sharp tuple and is
  not covered.

## What remains

Nothing for the 456 endpoint itself. Build times above were measured on a memory-constrained machine and vary by a factor of several with memory pressure.
