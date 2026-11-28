import New.Appendix.DiscreteSeries.SteepParameters
import New.UpperBound.Objects.Columns
import New.UpperBound.Objects.Parameters

/-!
# Steep parameters of Y₀ and Ỹ^0_0; periods of Poincaré series of deep level

At every infinite place, the parameter of `Y₀` and minus the parameter of `Ỹ^0_0 = Y₀ ⊕ E ẽ` are
steep in the sense of `New.DiscreteSeries.IsSteep`. Separately, at deep level the period over `V`
of a Poincaré series on `V ⊕ ⟨1⟩` is approximated by the term of the identity coset.

## Main definitions and results

* `New.Data.exists_isSteep`: for one numbering of the indices, the parameter of `Y₀` (`z = false`)
  and minus that of `Ỹ^0_0` (`z = true`) satisfy `New.DiscreteSeries.IsSteep` at every infinite
  place `τ`. That is, the highest weight `New.HCParam.lowestKType` of the lowest `K`-type vanishes
  on a block of indices of sign `+`. On the other indices the signs alternate and it decreases
  strictly within `[-3B, -B]`, `B = D.liftWeight 0 τ`. `New.Data.gridSigns` gives the signs and
  `New.Data.gridParam` twice these parameters.
* `New.Exchange.poincareKernel`: the function whose translates a Poincaré series sums. Its real
  factor here is `New.Exchange.translatedCoeff`, a translated product of matrix coefficients.
* `New.Space.IsLastColumn`: a rational vector of `V ⊕ ⟨1⟩` is the last column of a group element
  `γ`, that is, the vector `γ ẽ` for the last basis vector `ẽ`. Last columns index the cosets, and
  `New.Space.IsLastColumn.le_norm_archCoords_sub` separates them.
* `New.Exchange.norm_poincare_period_sub_le`: at deep level the period equals the term of the
  identity coset up to a small error.

Notions from other files:
* `New.Data.Φ`: the set of infinite places of the field `E` of the data `D`. Also, `D.ϱ` is the
  number of hyperbolic planes of `Y₀`, `D.InitIndex 0` the set of basis indices of `X₀` other than
  the last and `D.GridIndex z 0 0` the index set of `Y₀` or `Ỹ^0_0`.
* `Φ w` in the bounds `R ≤ ‖Φ w a‖`: the complex embedding of `E` at the infinite place `w`.
* `V.move x`, `vecAtPoint`, `archCoords`: the space `V` at the point `x` of the adelic group, the
  adelic coordinates of a rational vector there, and their infinite part as a Euclidean vector.
* `New.Data.liftWeight`: the number `κ_j(σ) = κ(σ) + (j + 1/2) Δ` at the infinite place `σ`, where
  `κ` is `D.weight`, `Δ = D.gap` the gap and `D.halfGap` half the gap.
* `New.GInf E s`: the product of one copy `New.USign s` of the complex unitary group `U(diag s)`
  for each infinite place of `E`. For an integer vector `l : New.HCParam s`, read as twice a
  Harish-Chandra parameter, `l.dsCoeff` is the Flensted-Jensen matrix coefficient on `U(diag s)`,
  and `l.HasLargeGap A` says that `l` has gap at least `500 n ^ 3 + A`, for `n` the rank.
* `New.signedSpace E s`: the standard space with matrix `diag(s)`; it needs a primitive root of
  unity of order `5040` in `E` (`New.HasPrimitiveRoot5040`).
* `New.Space.Γ`, `New.Space.quotMeasure`: the rational points of a hermitian space `V` inside the
  adelic unitary group `G E s`, and the measure on a fundamental domain for them.
* `New.principalLevel`: the finite adelic integral points congruent to `1` modulo an element `a`
  of the ring of integers of `E`.
-/

/-! ## Steepness of the discrete series parameters at infinite places -/

section SteepParameters

local grind_pattern New.Data.liftWeight_add_gap_le => D.liftWeight a τ, D.liftWeight b τ

/-- At an infinite place `τ`, let `ν` number the indices `D.GridIndex z 0 0` of the node `(0, 0)` of
the grid `Y` (`z = false`) or `Ỹ`, sending an index `y` to `i = ν y`. Assume its doubled parameter
`D.gridParam z 0 0 0 τ y` is `2 (D.targetParameter τ i) + z.toNat`. Assume its sign
`D.gridSigns z 0 0 0 y` is `entrySign 0 0 (i + 1 - k)`: `+` on the first `k - 1` entries (the near
entries, `i + 1 < k`; `k = D.k` is the rank of the source) and alternating on the others. Let `L` be
`2 (D.targetParameter τ i) + z.toNat` minus twice the weight of the lowest `K`-type at `y`, and let
`N = D.r + z.toNat` be the number of indices. Then `|L| ≤ N`. At a near entry,
`L + N = N + min N k - 1 - 2 i - (N - k) % 2`. -/
lemma New.Data.abs_targetParameter_sub_lowestKType_le_and_eq {P : Parameters} (D : Data P)
    {z : Bool} {τ : D.Φ} {ν : D.GridIndex z 0 0 ≃ Fin (D.r + z.toNat)}
    (h_entry : ∀ x : D.GridIndex z 0 0,
      D.gridSigns z 0 0 0 x = entrySign 0 0 (ν x + 1 - D.k) ∧
      D.gridParam z 0 0 0 τ x = 2 * D.targetParameter τ (ν x) + z.toNat)
    (y : D.GridIndex z 0 0) :
    let L : ℤ := 2 * D.targetParameter τ (ν y) + z.toNat - 2 * (D.gridParam z 0 0 0 τ).lowestKType y
    let N : ℕ := D.r + z.toNat
    |L| ≤ N ∧ (ν y + 1 < D.k → L + N = ↑(N + N ⊓ D.k - 1 - 2 * ν y - (N - D.k) % 2)) := by
  -- `L` counts the entries below entry `ν y` minus those above, with the opposite count for the
  -- entries of the opposite sign. Induction on `N` computes it: a far entry lies below every near
  -- one, as `D.liftWeight 0 τ` is large against the gap, and far signs alternate.
  intro L N
  let count (a i : ℕ) : ℤ :=
    (if D.targetParameter τ i < D.targetParameter τ a then 1
      else if D.targetParameter τ a < D.targetParameter τ i then -1 else 0) *
    (if (i + 1 - D.k) % 2 = (a + 1 - D.k) % 2 then 1 else -1)
  have h_sq_le : D.gap ^ 2 ≤ D.liftWeight 0 τ := D.nat_le_of_hasLogBound
  have h_count (M a : ℕ) : |∑ i ∈ Finset.range M, count a i| ≤ M ∧ (a + 1 < D.k →
      ∑ i ∈ Finset.range M, count a i + M = ↑(M + M ⊓ D.k - 1 - 2 * a - (M - D.k) % 2)) := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ]
      grind (splits := 20) [targetParameter_eq]
  -- `entrySign 0 0 i` depends only on the parity of `i`
  have h_sign (i i' : ℕ) : entrySign 0 0 i = entrySign 0 0 i' ↔ i % 2 = i' % 2 := by
    have h_ne : (-1 : ℤˣ) ≠ 1 := by decide
    rw [entrySign_eq_ite, entrySign_eq_ite]
    grind
  have h_L : L = ∑ i ∈ Finset.range N, count (ν y) i := by
    simp only [L, two_mul_lowestKType (hasGap_gridParam ..), twoRho, Finset.card_filter,
      reindex_equiv ν.symm, h_entry, ν.apply_symm_apply, Nat.cast_sum, ← Finset.sum_sub_distrib]
    simp only [ne_eq, h_sign]
    rw [← Fin.sum_univ_eq_sum_range, sub_sub_eq_add_sub, add_sub_add_left_eq_sub,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by grind
  rw [h_L]
  exact h_count N (ν y)

/-- Let `D` be admissible data for the fixed parameters `P`. The parameter of the object `Y₀`
(`z = false`), of rank `D.r`, and minus that of `Ỹ^0_0 = Y₀ ⊕ E ẽ` (`z = true`, one more index),
whose doubles are `D.gridParam z 0 0 0 τ` (offset `0` at the node `(0, 0)`, lift number `0`), are
steep: for one numbering `e` of their indices, at every infinite place `τ`, the sign is `+` and the
weight of the lowest `K`-type is `0` on the block `D.InitIndex 0` of the basis indices of `X₀`
other than the last. On the other `2 ϱ + 2` (and for `Ỹ^0_0` one more) indices, `ϱ = D.ϱ` being the
number of hyperbolic planes of `Y₀`, the signs alternate and the weight decreases strictly within
`[-3 B, -B]`, where `B = D.liftWeight 0 τ` is the weight `κ + Δ / 2` for the weight `κ` and gap
`Δ` of the data. -/
lemma New.Data.exists_isSteep {P : Parameters} (D : Data P) (z : Bool) :
    ∃ e : D.InitIndex 0 ⊕ Fin (2 * D.ϱ + 2 + z.toNat) ≃ D.GridIndex z 0 0,
      ∀ τ : D.Φ, DiscreteSeries.IsSteep (D.gridParam z 0 0 0 τ) (D.liftWeight 0 τ) e := by
  -- Number the indices by `ν`. By `two_mul_lowestKType`, `2 * lowestKType` is the doubled parameter
  -- minus a signed count `L` of the entries below and above. The size of `L` is at most the number
  -- `N` of indices, small against the gaps of the far entries, and `L` cancels the doubled
  -- parameter on the first `k - 1` (near) entries.
  let ν : D.GridIndex z 0 0 ≃ Fin (D.r + z.toNat) := D.gridNumber z
  let e : D.InitIndex 0 ⊕ Fin (2 * D.ϱ + 2 + z.toNat) ≃ D.GridIndex z 0 0 :=
    finSumFinEquiv.trans ((finCongr (by grind [n])).trans ν.symm)
  have he_inl (x : D.InitIndex 0) : (ν (e (.inl x)) : ℕ) = x := by simp [e]
  have he_inr (i : Fin (2 * D.ϱ + 2 + z.toNat)) : (ν (e (.inr i)) : ℕ) = D.n 0 - 1 + i := by
    simp [e]
  refine ⟨e, fun τ ↦ ?_⟩
  have h_entry (x : D.GridIndex z 0 0) :
      D.gridSigns z 0 0 0 x = entrySign 0 0 (ν x + 1 - D.k) ∧
      D.gridParam z 0 0 0 τ x = 2 * D.targetParameter τ (ν x) + z.toNat := by
    cases z <;> aesop (add simp [gridSigns, gridParam, gridNumber])
  -- The far entries of `D.targetParameter τ` are `Δ / 2 - κ_j` with `j ≤ Δ`, and `κ_j` lies between
  -- `B = D.liftWeight 0 τ` and `D.liftWeight D.gap τ ≤ 2 * B`.
  have h_sq_le : D.gap ^ 2 ≤ D.liftWeight 0 τ := D.nat_le_of_hasLogBound
  have h_far : D.liftWeight D.gap τ ≤ 2 * D.liftWeight 0 τ := by grind
  have h_count (y : D.GridIndex z 0 0) :
      let L : ℤ :=
        2 * D.targetParameter τ (ν y) + z.toNat - 2 * (D.gridParam z 0 0 0 τ).lowestKType y
      let N : ℕ := D.r + z.toNat
      |L| ≤ N ∧ (ν y + 1 < D.k → L + N = ↑(N + N ⊓ D.k - 1 - 2 * ν y - (N - D.k) % 2)) :=
    D.abs_targetParameter_sub_lowestKType_le_and_eq h_entry y
  -- The signs come from `h_entry`. Then `h_count` gives `lowestKType = 0` on the near entries, and
  -- on the far entries `lowestKType` strictly decreasing and within `[-3 * B, -B]`.
  refine ⟨fun x ↦ ?_, fun i ↦ ?_, fun x ↦ ?_, fun i i' h_lt ↦ ?_, fun i ↦ ?_⟩
  · grind [entrySign_eq_ite]
  · rw [neg_one_pow_eq_ite]
    grind [entrySign_eq_ite]
  · grind [targetParameter_eq, Bool]
  · grind [targetParameter_eq, Bool]
  · have h_mem : -(3 * D.liftWeight 0 τ : ℤ) ≤ (D.gridParam z 0 0 0 τ).lowestKType (e (.inr i)) ∧
        (D.gridParam z 0 0 0 τ).lowestKType (e (.inr i)) ≤ -(D.liftWeight 0 τ : ℤ) := by
      grind [targetParameter_eq, Bool]
    rw [Set.mem_Icc, neg_mul]
    exact_mod_cast h_mem

end SteepParameters

/-!
## Periods of Poincaré series of deep level

The cosets are indexed by their last columns. The last columns of those that meet the level
condition are well separated, so a packing bound controls the sum of the terms other than that of
the identity.
-/

section DeepLevelPeriod

open New MeasureTheory Matrix Space G EuclideanSpace Fintype Set Measure Subtype U Norms.L2Operator
  ComplexConjugate

/-- Unfolding: the translates by the rational points `V.Γ` of an integrable function on the adelic
group are integrable for the quotient measure, and their integrals sum to its integral. -/
lemma New.Space.hasSum_integral_translates {E n : Type} {s : n → ℤˣ} [Field E] [CMType E]
    [Fintype n] [DecidableEq n] (V : Space E n s) {𝕜 : Type*} [RCLike 𝕜]
    {f : G E s → 𝕜} (hf : Integrable f) :
    (∀ δ : V.Γ, Integrable (fun h : G E s ↦ f (δ * h)) V.quotMeasure) ∧
    HasSum (fun δ : V.Γ ↦ ∫ h : G E s, f (δ * h) ∂V.quotMeasure) (∫ g : G E s, f g) := by
  -- `(δ, h) ↦ δ * h` carries `count × quotMeasure` to Haar measure
  obtain ⟨h_int, h_eq⟩ :
      Integrable (fun p : V.Γ × G E s ↦ f (p.1 * p.2)) (Measure.count.prod V.quotMeasure) ∧
      ∫ δ : V.Γ, ∫ h : G E s, f (δ * h) ∂V.quotMeasure ∂Measure.count = ∫ g : G E s, f g :=
    (measurePreserving_orbitMeasure.comp (measurePreserving_swap (ν := V.quotMeasure))).fubini hf
  exact ⟨by simpa using h_int.prod_right_ae,
    by simpa [← h_eq] using! hasSum_integral_measure h_int.integral_prod_left⟩

section RealSlices

/-- The product over the infinite places `w` of the conjugate of the Flensted-Jensen matrix
coefficient `(l w).dsCoeff` of the doubled parameter `l w`, evaluated at `(α w)⁻¹ * g w * ω w`. -/
noncomputable def New.Exchange.translatedCoeff {E : Type*} {n : Type} {s : n → ℤˣ} [Field E]
    [CMType E] [Fintype n] [DecidableEq n] (l : NumberField.InfinitePlace E → HCParam s)
    (α ω g : GInf E s) : ℂ :=
  ∏ w : NumberField.InfinitePlace E, conj ((l w).dsCoeff ((α w)⁻¹ * g w * ω w : USign s))

/-- The constant in the decay of the slices of `translatedCoeff l α ω`: the product over the
infinite places `w` of `(2 (‖α w‖ ‖ω w‖)²) ^ A` and `16 ^ A` times the volume of the unit ball
around `1` in `U(s)`. -/
noncomputable def New.Exchange.sliceConst {E : Type*} {n : Type} {s : n → ℤˣ} [Field E]
    [CMType E] [Fintype n] [DecidableEq n] (A : ℕ) (α ω : GInf E (s ⊕ᵥ (1 : Unit → ℤˣ))) : ℝ :=
  ∏ w : NumberField.InfinitePlace E,
    (2 * (‖(α w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ *
      ‖(ω w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖) ^ 2) ^ A *
    (16 ^ A * volume.real {r : USign s | ‖(r : Matrix n n ℂ) - 1‖ ≤ 1})

/-- Decay of a translated matrix coefficient on `U(diag s)`: if `l` has a large gap for `2 A`, then
the norm of `l.dsCoeff` at `α⁻¹ x ω` is at most `(2 (‖α‖ ‖ω‖)²) ^ A * (2 / ‖x‖) ^ A * ‖x‖⁻¹ ^ A`
in the operator norm. -/
lemma New.Exchange.norm_dsCoeff_translate_le {n : Type} {s : n → ℤˣ} [Fintype n] [DecidableEq n]
    [Nonempty n] {A : ℕ} {l : HCParam s} (h_gap : l.HasLargeGap (2 * A)) (α x ω : USign s) :
    ‖l.dsCoeff (α⁻¹ * x * ω : USign s)‖ ≤
      (2 * (‖(α : Matrix n n ℂ)‖ * ‖(ω : Matrix n n ℂ)‖) ^ 2) ^ A *
        (2 / ‖(x : Matrix n n ℂ)‖) ^ A * ‖(x : Matrix n n ℂ)‖⁻¹ ^ A := by
  -- `x = α (α⁻¹ x ω) ω⁻¹` bounds the norm of `α⁻¹ x ω` below, and the coefficient decays in it.
  have h_norm : ‖x.val.val‖ ≤ ‖α.val.val‖ * ‖(α⁻¹ * x * ω).val.val‖ * ‖ω.val.val‖ := by
    grw [← U.norm_inv ω, ← norm_mul₃_le]
    simp [mul_assoc]
  have h_div : 2 / ‖(α⁻¹ * x * ω).val.val‖ ≤ 2 * (‖α.val.val‖ * ‖ω.val.val‖) / ‖x.val.val‖ := by
    rw [div_le_div_iff₀ (Units.norm_pos _) (Units.norm_pos _)]
    linarith
  calc ‖l.dsCoeff (α⁻¹ * x * ω : USign s)‖
    _ ≤ (2 / ‖(α⁻¹ * x * ω).val.val‖) ^ (2 * A) :=
      DiscreteSeries.norm_dsCoeff_le_pow h_gap le_add_self (α⁻¹ * x * ω)
    _ ≤ (2 * (‖α.val.val‖ * ‖ω.val.val‖) / ‖x.val.val‖) ^ (2 * A) :=
      pow_le_pow_left₀ (by positivity) h_div _
    _ = (2 * (‖α.val.val‖ * ‖ω.val.val‖) ^ 2 * (2 / ‖x.val.val‖) * ‖x.val.val‖⁻¹) ^ A := by
      rw [pow_mul]
      congr 1
      ring
    _ = (2 * (‖α.val.val‖ * ‖ω.val.val‖) ^ 2) ^ A * (2 / ‖x.val.val‖) ^ A * ‖x.val.val‖⁻¹ ^ A := by
      rw [mul_pow _ ‖x.val.val‖⁻¹, mul_pow _ (2 / ‖x.val.val‖)]

/-- Let `E` be a CM field. Let each parameter `l w` have a large gap for `2 A` (gap at least
`500 N ^ 3 + 2 A` for `N = card n + 1`), and let `A > 8 N²`. Let `inl s 1` be the block embedding
`r ↦ diag(r, 1)`. Let `t > 0` bound below the products over the infinite places `w` of the operator
norms of `g w * inl s 1 (r w)`. The function `translatedCoeff l α ω` is the product over the places
of the conjugates of the discrete series matrix coefficients of parameters `l w`, taken at
`(α w)⁻¹ * g w * ω w`. Its slice `r ↦ translatedCoeff l α ω (g * inl s 1 ∘ r)` is integrable on the
real group `GInf E s` (one copy of `U(diag s)` for each place). The integral of its norm is at most
`sliceConst A α ω * t⁻¹ ^ A`. -/
lemma New.Exchange.integrable_translatedCoeff_and_integral_norm_le {E : Type*} {n : Type}
    {s : n → ℤˣ} [Field E] [CMType E] [Fintype n] [DecidableEq n] {A : ℕ}
    {l : NumberField.InfinitePlace E → HCParam (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (hA_sq : 8 * (card n + 1) ^ 2 < A)
    (h_gap : ∀ w : NumberField.InfinitePlace E, (l w).HasLargeGap (2 * A))
    (ω α g : GInf E (s ⊕ᵥ (1 : Unit → ℤˣ))) {t : ℝ} (ht : 0 < t)
    (ht_le : ∀ r : GInf E s,
      t ≤ ∏ w : NumberField.InfinitePlace E,
        ‖((g w * inl s 1 (r w) : USign (s ⊕ᵥ 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖) :
    Integrable (fun r : GInf E s ↦ translatedCoeff l α ω (g * inl s 1 ∘ r)) ∧
    ∫ r : GInf E s, ‖translatedCoeff l α ω (g * inl s 1 ∘ r)‖ ≤ sliceConst A α ω * t⁻¹ ^ A := by
  let ψ (r : GInf E s) : ℂ := ∏ w : NumberField.InfinitePlace E,
    conj ((l w).dsCoeff ((α w)⁻¹ * (g w * inl s 1 (r w)) * ω w : USign (s ⊕ᵥ 1)))
  let B (w : NumberField.InfinitePlace E) : ℝ := (2 * (‖(α w).val.val‖ * ‖(ω w).val.val‖) ^ 2) ^ A
  change Integrable ψ ∧ ∫ r : GInf E s, ‖ψ r‖ ≤ (∏ w : NumberField.InfinitePlace E,
    B w * (16 ^ A * volume.real {r : USign s | ‖(r : Matrix n n ℂ) - 1‖ ≤ 1})) * t⁻¹ ^ A
  let D (w : NumberField.InfinitePlace E) (r : USign s) : ℝ :=
    (2 / ‖(inl s 1 r * (g w)⁻¹).val.val‖) ^ A
  have decay (w : NumberField.InfinitePlace E) :
      Integrable (D w) ∧
      ∫ r : USign s, D w r ≤
        16 ^ A * volume.real {r : USign s | ‖(inl s (1 : Unit → ℤˣ) r).val.val - 1‖ ≤ 1} :=
    DiscreteSeries.integral_decay_le volume DiscreteSeries.isProperMap_inl (by simpa) (g w)⁻¹
  -- the coefficient decays with exponent `2 A`: one half gives `t⁻¹ ^ A`, the other half `D`
  have pointwise (r : GInf E s) :
      ‖ψ r‖ ≤ (∏ w : NumberField.InfinitePlace E, B w * D w (r w)⁻¹) * t⁻¹ ^ A := by
    grw [ht_le r, ← Finset.prod_inv_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
      norm_prod]
    gcongr with w
    have norm_eq : ‖(inl s 1 (r w)⁻¹ * (g w)⁻¹).val.val‖ = ‖(g w * inl s 1 (r w)).val.val‖ := by
      rw [map_inv, ← _root_.mul_inv_rev, U.norm_inv]
    rw [Complex.norm_conj]
    simp only [B, D, norm_eq]
    exact norm_dsCoeff_translate_le (h_gap w) (α w) (g w * inl s 1 (r w)) (ω w)
  have major_int : Integrable fun r : GInf E s ↦
      (∏ w : NumberField.InfinitePlace E, B w * D w (r w)⁻¹) * t⁻¹ ^ A :=
    (Integrable.fintype_prod fun w ↦ (decay w).1.comp_inv.const_mul (B w)).mul_const _
  refine ⟨major_int.mono' (by fun_prop : Continuous ψ).aestronglyMeasurable
    (ae_of_all _ pointwise), ?_⟩
  grw [integral_mono_of_nonneg (.of_forall (by simp)) major_int (ae_of_all _ pointwise)]
  rw [integral_mul_const, integral_fintype_prod_volume_eq_prod fun w r ↦ B w * D w r⁻¹]
  simp_rw [integral_const_mul, integral_inv_eq_self]
  gcongr with w
  simpa [← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add] using (decay w).2

end RealSlices

/-- The embedding `h ↦ h ⊕ 1` of the unitary group of signs `s` in that of signs `s ⊕ 1`. Its
image fixes the last basis vector. -/
noncomputable def New.G.inlLine (E : Type) {n : Type} (s : n → ℤˣ) [Field E] [CMType E]
    [Fintype n] [DecidableEq n] : G E s →* G E (s ⊕ᵥ (1 : Unit → ℤˣ)) :=
  sum.comp (.inl (G E s) (G E 1))

/-- The block matrix `h ⊕ 1` has principal level `a` if and only if `h` has. -/
lemma New.G.inlLine_snd_mem_principalLevel_iff {E n : Type} {s : n → ℤˣ} [Field E] [CMType E]
    [Fintype n] [DecidableEq n] {a : NumberField.RingOfIntegers E} (h : G E s) :
    (inlLine E s h).2 ∈ principalLevel (n ⊕ Unit) a ↔ h.2 ∈ principalLevel n a := by
  have zero_dvd (c : 𝔸f E) : ∃ y ∈ Ô E, 0 = c * y := ⟨0, by simp⟩
  simp [principalLevel, mem_stdLevel, ← adeleMatrix_snd, inlLine, zero_dvd, Subgroup.copy,
    Matrix.one_apply]

/-- The rational vector `y` of `V ⊕ ⟨1⟩` is the last column of `γ`: in the coordinates at any point
`u` it is the last column of the adelic matrix of `u⁻¹ γ (k ⊕ 1)`, for every `k`. Here `⟨1⟩` is
the standard line `signedSpace E 1`; it needs a primitive root of unity of order `5040` in `E`. -/
def New.Space.IsLastColumn {E n : Type} {s : n → ℤˣ} [Field E] [CMType E] [Fintype n]
    [DecidableEq n] [HasPrimitiveRoot5040 E] (V : Space E n s)
    (γ : G E (s ⊕ᵥ (1 : Unit → ℤˣ))) (y : n ⊕ Unit → E) : Prop :=
  ∀ (k : G E s) (u : G E (s ⊕ᵥ (1 : Unit → ℤˣ))),
    ((V.sum (signedSpace (n := Unit) E 1)).move u).vecAtPoint y =
      (u⁻¹ * γ * inlLine E s k).adeleMatrix *ᵥ Pi.single (.inr ()) 1

/-- If `E` has a primitive root of unity of order `5040`, every rational point `γ` of `V ⊕ ⟨1⟩`
has a last column: a rational vector whose coordinates are those of the image under `γ` of the
last basis vector. -/
lemma New.Space.exists_isLastColumn {E n : Type} {s : n → ℤˣ} [Field E]
    [CMType E] [Fintype n] [DecidableEq n] [HasPrimitiveRoot5040 E] (V : Space E n s)
    (γ : (V.sum (signedSpace (n := Unit) E 1)).Γ) : ∃ y : n ⊕ Unit → E, V.IsLastColumn γ y := by
  obtain ⟨_, g, rfl⟩ := γ
  refine ⟨g.val.val *ᵥ (0 ⊕ᵥ 1), fun k u ↦ ?_⟩
  -- `0 ⊕ 1` has as coordinates the last basis vector, which `k ⊕ 1` fixes
  have column_eq : (inlLine E s k).adeleMatrix *ᵥ Pi.single (.inr ()) 1 =
      (V.sum (signedSpace (n := Unit) E 1)).vecAtPoint (0 ⊕ᵥ 1) := by
    rw [sum_vecAtPoint]
    simp [funext_iff, inlLine, Space.vecAtPoint, signedSpace]
  rw [vecAtPoint_move, ← ratEmbed_mulVec_vecAtPoint, ← column_eq, mulVec_mulVec, mulVec_mulVec]
  simp [mul_assoc]

/-- If `γ` and `γ'` have the same last column `y` (`V.IsLastColumn`), then `γ⁻¹ * γ'` lies in the
image of `inlLine E s`. -/
lemma New.Space.IsLastColumn.inv_mul_mem_range {E n : Type} {s : n → ℤˣ} [Field E]
    [CMType E] [Fintype n] [DecidableEq n] [HasPrimitiveRoot5040 E] {V : Space E n s}
    {γ γ' : G E (s ⊕ᵥ (1 : Unit → ℤˣ))} {y : n ⊕ Unit → E} (hγ : V.IsLastColumn γ y)
    (hγ' : V.IsLastColumn γ' y) : γ⁻¹ * γ' ∈ (inlLine E s).range := by
  -- both send the last basis vector to the coordinates of `y`
  have fixes : (γ⁻¹ * γ').adeleMatrix *ᵥ Pi.single (.inr ()) 1 = Pi.single (.inr ()) 1 := by
    have h_col : (γ⁻¹ * γ' * inlLine E s 1).adeleMatrix *ᵥ Pi.single (.inr ()) 1 =
        (γ⁻¹ * γ * inlLine E s 1).adeleMatrix *ᵥ Pi.single (.inr ()) 1 :=
      (hγ' 1 γ).symm.trans (hγ 1 γ)
    simpa [-mulVec_single] using h_col
  obtain ⟨g, hg⟩ : ∃ g, U.sum stdForm_sum (g, 1) = G.toUnitary (γ⁻¹ * γ') := by
    refine (mem_range_sum_left stdForm_sum (by simp)).2 ?_
    simpa [adeleMatrix, ← ext_iff, funext_iff, Unique.forall_iff] using fixes
  refine ⟨G.toUnitary.symm g, G.toUnitary.injective ?_⟩
  rw [← hg]
  -- both elements have the block matrix `diag(g, 1)`
  have h_blocks : (G.toUnitary (inlLine E s (G.toUnitary.symm g))).val.val =
      fromBlocks (G.toUnitary.symm g).adeleMatrix 0 0 1 :=
    (adeleMatrix_sum _).trans (by simp)
  exact Subtype.ext (Units.ext h_blocks)

/-- Separation of last columns, for `E` with a primitive root of unity of order `5040`. Let
`y ≠ y'` be the last columns of `γ` and `γ'`, and let `(x ⊕ 1)⁻¹ γ (k ⊕ 1)` and
`(x ⊕ 1)⁻¹ γ' (k' ⊕ 1)` have finite part of level `a ≠ 0`. If `|a| ≥ R ≥ 0` at all infinite
places, the distance of `y` and `y'` at the point `x ⊕ 1` is at least `R` times the first minimum
of `V` at `x`: the least length of a nonzero lattice vector there, cut off at `1`. -/
lemma New.Space.IsLastColumn.le_norm_archCoords_sub {E n : Type} {s : n → ℤˣ} [Field E]
    [CMType E] [Fintype n] [DecidableEq n] [HasPrimitiveRoot5040 E]
    {V : Space E n s} {γ γ' : G E (s ⊕ᵥ (1 : Unit → ℤˣ))} {y y' : n ⊕ Unit → E}
    (hγ : V.IsLastColumn γ y) (hγ' : V.IsLastColumn γ' y') (h_ne : y ≠ y')
    {a : NumberField.RingOfIntegers E} (ha : a ≠ 0) {x k k' : G E s}
    (hk : ((inlLine E s x)⁻¹ * γ * inlLine E s k).2 ∈ principalLevel (n ⊕ Unit) a)
    (hk' : ((inlLine E s x)⁻¹ * γ' * inlLine E s k').2 ∈ principalLevel (n ⊕ Unit) a) {R : ℝ}
    (hR_nonneg : 0 ≤ R) (hR_le : ∀ w : NumberField.InfinitePlace E, R ≤ ‖Φ w (a : E)‖) :
    R * (V.move x).firstMinimum ≤
      ‖((V.sum (signedSpace (n := Unit) E 1)).move (inlLine E s x)).archCoords (y - y')‖ := by
  set Zx := (V.sum (signedSpace (n := Unit) E 1)).move (inlLine E s x)
  obtain ⟨w, hw⟩ : ∃ w : n ⊕ Unit → E, a.val • w = y - y' :=
    MulAction.surjective₀ (a.ext.mt ha) (y - y')
  have w_ne : w ≠ 0 := fun h_zero ↦ h_ne (sub_eq_zero.1 (by simp [← hw, h_zero]))
  -- both columns are congruent to the last basis vector mod `a`, so `w` is a lattice vector
  have w_mem : w ∈ Zx.baseLattice := by
    intro i
    obtain ⟨t, t_mem, ht⟩ := hk.2 i (.inr ())
    obtain ⟨t', t'_mem, ht'⟩ := hk'.2 i (.inr ())
    convert sub_mem t_mem t'_mem
    apply (isUnit_algebraMap_finAdele ha).mul_left_cancel
    have h_entry : (Zx.vecAtPoint (a.val • w) i).2 = (Zx.vecAtPoint (y - y') i).2 := by rw [hw]
    -- the left side is `a * (vecAtPoint w i)`, the right one the difference of the two entries
    have h_left : (Zx.vecAtPoint (a.val • w) i).2 =
        algebraMap (NumberField.RingOfIntegers E) (𝔸f E) a * (Zx.vecAtPoint w i).2 := by
      simp [↓map_smulₛₗ, IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers E) E (𝔸f E)]
    have h_right : (Zx.vecAtPoint (y - y') i).2 =
        algebraMap (NumberField.RingOfIntegers E) (𝔸f E) a * (t - t') := by
      simp [Zx, hγ k, hγ' k', mul_sub, ← ht, ← ht', -adeleMatrix_mul]
    exact h_left.symm.trans (h_entry.trans h_right)
  -- the definite summand `⟨1⟩` has no short vector, so it does not lower the first minimum
  have firstMinimum_le_sum : (V.move x).firstMinimum ≤ Zx.firstMinimum := by
    refine .trans (le_inf le_rfl ?_) Rows.inf_le_firstMinimum_sum
    exact firstMinimum_le_one.trans (one_le_firstMinimum fun _ _ ↦ rfl)
  -- a nonzero lattice vector has norm at least `firstMinimum`; `a` stretches it by at least `R`
  calc
    R * (V.move x).firstMinimum ≤ R * ‖Zx.archCoords w‖ := by
      grw [firstMinimum_le_sum, firstMinimum_le w_mem w_ne]
    _ ≤ ‖Zx.archCoords (a.val • w)‖ := by
      rw [← norm_smul_of_nonneg hR_nonneg, norm_eq, norm_eq]
      gcongr with p
      -- the coordinates at the place `p.1` are stretched by `|a|`, which is at least `R`
      simpa [archCoords, -algebraMap_smul, abs_of_nonneg hR_nonneg] using
        mul_le_mul_of_nonneg_right (hR_le p.1) (norm_nonneg _)
    _ = ‖Zx.archCoords (y - y')‖ := by rw [hw]

/-- If `y` is the last column of `1` in `V ⊕ ⟨1⟩` (`hy : V.IsLastColumn 1 y`), then in the space
moved to the point `x ⊕ 1` the length of `y` (the norm of `archCoords y`) is at most the number of
infinite places of `E`. -/
lemma New.Space.IsLastColumn.norm_archCoords_one_le {E n : Type} {s : n → ℤˣ} [Field E]
    [CMType E] [Fintype n] [DecidableEq n] [HasPrimitiveRoot5040 E]
    {V : Space E n s} {y : n ⊕ Unit → E}
    (hy : V.IsLastColumn 1 y) (x : G E s) :
    ‖((V.sum (signedSpace (n := Unit) E 1)).move (inlLine E s x)).archCoords y‖ ≤
      Core.numInfPlaces E := by
  have sqrt_le : √(Core.numInfPlaces E : ℝ) ≤ Core.numInfPlaces E := by
    simp [Real.sqrt_le_self_iff, NeZero.one_le]
  simpa [hy x, archCoords, -adeleMatrix_mul, sum_prod_type, norm_eq] using sqrt_le

/-- At the point `x ⊕ 1`, the last column of `γ` has length at most the number of infinite places
times the product of the local operator norms of `(x ⊕ 1)⁻¹ γ (k ⊕ 1)`, for every `k`. -/
lemma New.Space.IsLastColumn.norm_archCoords_le {E n : Type} {s : n → ℤˣ} [Field E]
    [CMType E] [Fintype n] [DecidableEq n] [HasPrimitiveRoot5040 E] {V : Space E n s}
    {γ : G E (s ⊕ᵥ (1 : Unit → ℤˣ))} {y : n ⊕ Unit → E} (hy : V.IsLastColumn γ y) (x k : G E s) :
    ‖((V.sum (signedSpace (n := Unit) E 1)).move (inlLine E s x)).archCoords y‖ ≤
      (∏ w : NumberField.InfinitePlace E,
        ‖(((inlLine E s x)⁻¹ * γ * inlLine E s k).1 w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖) *
        Core.numInfPlaces E := by
  set Zx := (V.sum (signedSpace (n := Unit) E 1)).move (inlLine E s x)
  set g := (inlLine E s x)⁻¹ * γ * inlLine E s k
  obtain ⟨y₀, hy₀⟩ := V.exists_isLastColumn 1
  -- `g` maps the last column of `1` to that of `γ`
  have vec_eq : Zx.vecAtPoint y = (1 : ℕ) • g.adeleMatrix *ᵥ Zx.vecAtPoint y₀ := by
    rw [hy k, hy₀ x, mulVec_mulVec]
    simp [g]
  have norm_le : ‖Zx.archCoords y‖ ≤
      (1 : ℕ) * (∏ w : NumberField.InfinitePlace E, ‖(g.1 w).val.val‖) * ‖Zx.archCoords y₀‖ :=
    (mem_and_norm_le_of_vecAtPoint y Zx y₀ g.adeleMatrix 1 (le_prod_opNorm g.1).2 vec_eq).2
  grw [norm_le, hy₀.norm_archCoords_one_le x, Nat.cast_one, one_mul]

/-- Let `E` have a primitive root of unity of order `5040`. A sum over the rational points of
`V ⊕ ⟨1⟩` is a sum over the cosets of the rational points of `V`, embedded by
`inlLine E s : h ↦ h ⊕ 1`. Here `C` is a set of representatives, and `W ⊆ C` contains every `σ`
for which `p` is nonzero somewhere on `σ (G E s ⊕ 1)`, in adelic points. -/
lemma New.Space.tsum_eq_tsum_cosets {E n : Type} {s : n → ℤˣ} [Field E]
    [CMType E] [Fintype n] [DecidableEq n] [HasPrimitiveRoot5040 E] (V : Space E n s)
    {C : Set (V.sum (signedSpace (n := Unit) E 1)).Γ}
    (hC : Subgroup.IsComplement C
      ((inlLine E s).range.subgroupOf (V.sum (signedSpace (n := Unit) E 1)).Γ))
    {W : Set C} {p : G E (s ⊕ᵥ (1 : Unit → ℤˣ)) → ℂ}
    (h_supp : ∀ (σ : C) (h : G E s), p (σ * inlLine E s h) ≠ 0 → σ ∈ W) :
    ∑' γ : (V.sum (signedSpace (n := Unit) E 1)).Γ, p γ =
      ∑' q : W × V.Γ, p (q.1 * inlLine E s q.2) := by
  set Z := V.sum (signedSpace (n := Unit) E 1)
  let emb (δ : V.Γ) : (inlLine E s).range.subgroupOf Z.Γ :=
    ⟨⟨inlLine E s δ, by simp [Z, inlLine, sum_mem_Gamma]⟩, δ, rfl⟩
  have emb_inj : emb.Injective := fun δ δ' h_eq ↦ by
    simpa [emb, inlLine, isClosedEmbedding_sum.injective.eq_iff] using h_eq
  let mul (q : W × V.Γ) : Z.Γ := q.1 * emb q.2
  have mul_inj : mul.Injective := fun q q' (h_eq : mul q = mul q') ↦
    Subtype.val_injective.prodMap emb_inj (hC.1 h_eq)
  have support_le : Function.support (fun γ : Z.Γ ↦ p γ) ⊆ range mul := by
    -- every rational point is `σ * inlLine E s h` for some `σ` in `C`; as `h` is then rational
    -- and `p` vanishes unless `σ ∈ W`, the point is a value of `mul`
    refine hC.2.forall.2 ?_
    rintro ⟨σ, ⟨_, h_rat⟩, h, ⟨⟩⟩ h_ne
    have h_mem_Γ : h ∈ V.Γ := ((sum_mem_Gamma ..).1 h_rat).1
    have σ_mem : σ ∈ W := h_supp σ h h_ne
    exact ⟨(⟨σ, σ_mem⟩, ⟨h, h_mem_Γ⟩), rfl⟩
  exact (mul_inj.tsum_eq support_le).symm

/-- Unfolding of a countable family `P` of integrable functions whose `L¹` norms are summable: the
integrals of the `P i` over the group sum to the integral over the quotient of the sum of all
translates of all `P i` by `V.Γ`. -/
lemma New.Space.hasSum_integral_of_summable_integral_norm {E n : Type} {s : n → ℤˣ} [Field E]
    [CMType E] [Fintype n] [DecidableEq n] (V : Space E n s) {ι : Type*} [Countable ι]
    {P : ι → G E s → ℂ} (hP_int : ∀ i : ι, Integrable (P i))
    (hP_sum : Summable fun i : ι ↦ ∫ h : G E s, ‖P i h‖) :
    HasSum (fun i : ι ↦ ∫ h : G E s, P i h)
      (∫ h : G E s, ∑' q : ι × V.Γ, P q.1 (q.2 * h) ∂V.quotMeasure) := by
  have unfold_norm (i : ι) : HasSum (fun δ : V.Γ ↦ ∫ h, ‖P i (δ * h)‖ ∂V.quotMeasure)
      (∫ h, ‖P i h‖) := (V.hasSum_integral_translates (hP_int i).norm).2
  have summable_norm : Summable fun q : ι × V.Γ ↦ ∫ h, ‖P q.1 (q.2 * h)‖ ∂V.quotMeasure := by
    refine (summable_prod_of_nonneg fun _ ↦ by positivity).2 ⟨fun i ↦ (unfold_norm i).summable, ?_⟩
    simpa only [fun i ↦ (unfold_norm i).tsum_eq] using hP_sum
  have translate_int (q : ι × V.Γ) : Integrable (fun h ↦ P q.1 (q.2 * h)) V.quotMeasure :=
    (V.hasSum_integral_translates (hP_int q.1)).1 q.2
  -- interchange the sum over all pairs `(i, δ)` with the integral
  have pair_sum : HasSum (fun q : ι × V.Γ ↦ ∫ h, P q.1 (q.2 * h) ∂V.quotMeasure)
      (∫ h, ∑' q : ι × V.Γ, P q.1 (q.2 * h) ∂V.quotMeasure) :=
    MeasureTheory.hasSum_integral_of_summable_integral_norm translate_int summable_norm
  -- for each `i`, the terms `(i, δ)` sum to the integral of `P i` over the group
  have fiber_sum (i : ι) : HasSum (fun δ : V.Γ ↦ ∫ h, P i (δ * h) ∂V.quotMeasure) (∫ h, P i h) :=
    (V.hasSum_integral_translates (hP_int i)).2
  exact pair_sum.prod_fiberwise fiber_sum

/-- The product of an integrable function on the real group and the indicator function of the level
`a ≠ 0` is integrable on the adelic group. -/
lemma New.Exchange.integrable_mul_indicator {E n : Type} {s : n → ℤˣ} [Field E] [CMType E]
    [Fintype n] [DecidableEq n] {a : NumberField.RingOfIntegers E} (ha : a ≠ 0)
    {ψ : GInf E s → ℂ} (hψ : Integrable ψ) :
    Integrable fun h : G E s ↦ ψ h.1 * indicator (principalLevel n a) 1 h.2 := by
  have level_int : Integrable (indicator (principalLevel n a : Set (Gf E n)) (1 : Gf E n → ℂ)) :=
    ((integrableOn_const (by simp)).mono_set principalLevel_le_stdLevel).integrable_indicator
      (isOpen_principalLevel ha).measurableSet
  exact hψ.mul_prod level_int

/-- The `L¹` norm of `ψ` times the indicator function of the level `a ≠ 0` is the `L¹` norm of
`ψ` on the real group times the volume of the level. -/
lemma New.Exchange.integral_norm_mul_indicator {E n : Type} {s : n → ℤˣ} [Field E] [CMType E]
    [Fintype n] [DecidableEq n] {a : NumberField.RingOfIntegers E} (ha : a ≠ 0) (ψ : GInf E s → ℂ) :
    ∫ h : G E s, ‖ψ h.1 * indicator (principalLevel n a) 1 h.2‖ =
      (∫ r : GInf E s, ‖ψ r‖) * volume.real (principalLevel n a : Set (Gf E n)) := by
  simp_rw [norm_mul, volume_eq_prod, norm_indicator_eq_indicator_norm]
  rw [integral_prod_mul fun r ↦ ‖ψ r‖]
  simp [(isOpen_principalLevel ha).measurableSet]

/-- For `F` of level `a`, the integral of `ψ` times the indicator function of the level against the
translate of `F` by `x` is the volume of the level times `realConv ψ F x`, the integral of
`r ↦ ψ r * F (x * (r, 1))` over the real group (right convolution). -/
lemma New.Exchange.integral_mul_indicator_mul_eq_smul_realConv {E n : Type} {s : n → ℤˣ} [Field E]
    [CMType E] [Fintype n] [DecidableEq n] {F : G E s → ℂ}
    {a : NumberField.RingOfIntegers E} (ha : a ≠ 0) (hF_level : HasLevel F (principalLevel n a))
    (ψ : GInf E s → ℂ) (x : G E s) :
    ∫ h : G E s, ψ h.1 * indicator (principalLevel n a) 1 h.2 * F (x * h) =
      volume.real (principalLevel n a : Set (Gf E n)) • realConv ψ F x := by
  have split (h : G E s) : ψ h.1 * indicator (principalLevel n a) 1 h.2 * F (x * h) =
      ψ h.1 * F (x * (h.1, 1)) * indicator (principalLevel n a) (fun _ ↦ 1) h.2 := by
    by_cases h_mem : h.2 ∈ principalLevel n a
    · simp [h_mem, ← hF_level _ h_mem (x * (h.1, 1)), mul_assoc]
    · simp [h_mem]
  simp_rw [split, volume_eq_prod]
  rw [integral_prod_mul fun r ↦ ψ r * F (x * (r, 1)),
    integral_indicator_const _ (isOpen_principalLevel ha).measurableSet, mul_smul_one]
  rfl

/-- The kernel of a Poincaré series: the function `φ` of the real part of `g` times the indicator
function of the level `K` at its finite part. -/
noncomputable def New.Exchange.poincareKernel {E n : Type} {s : n → ℤˣ} [Field E] [CMType E]
    [Fintype n] [DecidableEq n] (φ : GInf E s → ℂ) (K : Subgroup (Gf E n)) (g : G E s) : ℂ :=
  φ g.1 * indicator K 1 g.2

/-- Let `E` be a CM field and let the finite part of `g` have principal level `a`. Then the kernel
of level `a` at `g (h ⊕ 1)` is the value of `φ` at the real part of `g (h ⊕ 1)` times the indicator
function of the level `a` at the finite part of `h`. -/
lemma New.Exchange.poincareKernel_mul_inlLine {E n : Type} {s : n → ℤˣ} [Field E] [CMType E]
    [Fintype n] [DecidableEq n] (φ : GInf E (s ⊕ᵥ (1 : Unit → ℤˣ)) → ℂ)
    {a : NumberField.RingOfIntegers E} {g : G E (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (hg : g.2 ∈ principalLevel (n ⊕ Unit) a) (h : G E s) :
    poincareKernel φ (principalLevel (n ⊕ Unit) a) (g * inlLine E s h) =
      φ (g.1 * inl s 1 ∘ h.1) * indicator (principalLevel n a) 1 h.2 := by
  have real_eq : (g * inlLine E s h).1 = g.1 * inl s 1 ∘ h.1 := rfl
  have mem_iff :
      g.2 * (inlLine E s h).2 ∈ principalLevel (n ⊕ Unit) a ↔ h.2 ∈ principalLevel n a :=
    (mul_mem_cancel_left hg).trans (inlLine_snd_mem_principalLevel_iff h)
  by_cases h_mem : h.2 ∈ principalLevel n a <;> simp [poincareKernel, real_eq, h_mem, mem_iff]

/-- Decay of one term of a Poincaré series over a CM field `E`. The kernel `poincareKernel φ K g` is
`φ` at the real part of `g` times the indicator function of `K` at its finite part. Here
`φ = translatedCoeff l α ω` is the product over the infinite places `w` of the conjugated discrete
series coefficients of parameters `l w` at `(α w)⁻¹ * g w * ω w`, and `K` is the principal level
`a`. Let each `l w` have a large gap for `2 A`, with `A > 8 (card n + 1)²`, and let `g (k ⊕ 1)` have
finite part of level `a ≠ 0`. Let `t > 0` bound below the products over the infinite places of the
operator norms of `g (h ⊕ 1)`. Then the kernel at `g (h ⊕ 1)` is integrable in `h`. Its `L¹` norm is
at most the volume of the principal level `a` in `Gf E n` times `sliceConst A α ω * t⁻¹ ^ A`. -/
lemma New.Exchange.integral_norm_poincareKernel_le {E n : Type} {s : n → ℤˣ} [Field E] [CMType E]
    [Fintype n] [DecidableEq n] {a : NumberField.RingOfIntegers E} (ha : a ≠ 0)
    {A : ℕ} {l : NumberField.InfinitePlace E → HCParam (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (hA_sq : 8 * (card n + 1) ^ 2 < A)
    (h_gap : ∀ w : NumberField.InfinitePlace E, (l w).HasLargeGap (2 * A))
    (ω α : GInf E (s ⊕ᵥ (1 : Unit → ℤˣ))) {g : G E (s ⊕ᵥ (1 : Unit → ℤˣ))} {k : G E s}
    (hk : (g * inlLine E s k).2 ∈ principalLevel (n ⊕ Unit) a) {t : ℝ} (ht : 0 < t)
    (ht_le : ∀ h : G E s, t ≤ ∏ w : NumberField.InfinitePlace E,
      ‖((g * inlLine E s h).1 w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖) :
    Integrable (fun h : G E s ↦
      poincareKernel (translatedCoeff l α ω) (principalLevel (n ⊕ Unit) a) (g * inlLine E s h)) ∧
    ∫ h : G E s,
        ‖poincareKernel (translatedCoeff l α ω) (principalLevel (n ⊕ Unit) a) (g * inlLine E s h)‖ ≤
      volume.real (principalLevel n a : Set (Gf E n)) * sliceConst A α ω * t⁻¹ ^ A := by
  -- Translated by `k`, the kernel is the slice `ψ` times the indicator function of the level.
  let kernel (h : G E s) : ℂ :=
    poincareKernel (translatedCoeff l α ω) (principalLevel (n ⊕ Unit) a) (g * inlLine E s h)
  let ψ (r : GInf E s) : ℂ := translatedCoeff l α ω ((g * inlLine E s k).1 * inl s 1 ∘ r)
  have kernel_eq (h : G E s) : kernel (k * h) = ψ h.1 * indicator (principalLevel n a) 1 h.2 := by
    simp only [kernel, map_mul, ← mul_assoc]
    exact poincareKernel_mul_inlLine _ hk h
  have slice_ge (r : GInf E s) : t ≤ ∏ w : NumberField.InfinitePlace E,
      ‖((g * inlLine E s k).1 w * inl s 1 (r w)).val.val‖ := by
    have h_le := ht_le (k * (r, 1))
    rwa [map_mul, ← mul_assoc] at h_le
  obtain ⟨ψ_int, ψ_le⟩ : Integrable ψ ∧ ∫ r : GInf E s, ‖ψ r‖ ≤ sliceConst A α ω * t⁻¹ ^ A :=
    integrable_translatedCoeff_and_integral_norm_le hA_sq h_gap ω α _ ht slice_ge
  have shifted_int : Integrable fun h : G E s ↦ kernel (k * h) := by
    simpa only [kernel_eq] using integrable_mul_indicator ha ψ_int
  refine ⟨by simpa using shifted_int.comp_mul_left k⁻¹, ?_⟩
  calc ∫ h : G E s, ‖kernel h‖
    _ = ∫ h : G E s, ‖kernel (k * h)‖ := (integral_mul_left_eq_self (‖kernel ·‖) k).symm
    _ = (∫ r : GInf E s, ‖ψ r‖) * volume.real (principalLevel n a : Set (Gf E n)) := by
      simp_rw [kernel_eq]
      exact integral_norm_mul_indicator ha ψ
    _ ≤ volume.real (principalLevel n a : Set (Gf E n)) * sliceConst A α ω * t⁻¹ ^ A := by
      grw [ψ_le, mul_comm, mul_assoc]

/-- The packing bound. Let the points `col i` of a real normed space of finite dimension at most
`A - 2` have mutual distances at least `d²`, and let `‖col base‖ ≤ d` with `d ≥ 10`. Then the sum
of `(d / ‖col i‖) ^ A` over `i ≠ base` converges and is at most `10 / d`. -/
lemma New.Exchange.tsum_div_norm_pow_le_of_separated {ι X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] {col : ι → X} {base : ι} {d : ℝ} {A : ℕ}
    (hd_ten_le : 10 ≤ d) (h_sep : Pairwise fun i j : ι ↦ d ^ 2 ≤ ‖col i - col j‖)
    (h_base : ‖col base‖ ≤ d) (hA : Module.finrank ℝ X + 2 ≤ A) :
    Summable (fun i : Elem {base}ᶜ ↦ (d / ‖col i‖) ^ A) ∧
    ∑' i : Elem {base}ᶜ, (d / ‖col i‖) ^ A ≤ 10 / d := by
  have d_pos : 0 < d := by linarith
  -- away from `base`, norms and mutual distances are at least `d ^ 2 / 2`
  have norm_ge (i : Elem {base}ᶜ) : d ^ 2 / 2 ≤ ‖col i‖ := by
    nlinarith only [h_sep i.property, norm_sub_le (col i) (col base), h_base, hd_ten_le]
  have dist_ge : Pairwise fun i j : Elem {base}ᶜ ↦ d ^ 2 / 2 ≤ ‖col i - col j‖ :=
    fun i j h_ne ↦ (half_le_self (sq_nonneg d)).trans (h_sep (mt Subtype.ext h_ne))
  obtain ⟨summable, tsum_le⟩ : Summable (fun i : Elem {base}ᶜ ↦ ‖col i‖⁻¹ ^ A) ∧
      ∑' i : Elem {base}ᶜ, ‖col i‖⁻¹ ^ A ≤ (5 / (d ^ 2 / 2)) ^ A :=
    tsum_inv_pow_le_of_separated (by positivity) dist_ge norm_ge hA
  simp_rw [div_eq_mul_inv d, mul_pow]
  refine ⟨summable.mul_left _, ?_⟩
  calc ∑' i : Elem {base}ᶜ, d ^ A * ‖col i‖⁻¹ ^ A
    _ ≤ (d * (5 / (d ^ 2 / 2))) ^ A := by grw [tsum_mul_left, tsum_le, mul_pow]
    _ = (10 / d) ^ A := by
      congr 1
      field
    _ ≤ 10 / d := pow_le_of_le_one (by positivity) ((div_le_one d_pos).2 hd_ten_le) (by omega)

/-- The period of a Poincaré series of deep level is its main term, up to a small error. Let `E`
have a primitive root of unity of order `5040` and let `F` be automorphic on `V` of level `a ≠ 0`
and bounded by `S`. Let the parameters `l w` for `V ⊕ ⟨1⟩` have a large gap for `2 A`, and let
`φ = translatedCoeff l α ω`, the product over the infinite places `w` of their conjugated discrete
series coefficients at `(α w)⁻¹ * g w * ω w`. Let `|a| ≥ R ≥ 0` at all infinite places and
`d² ≤ R λ`, where `λ = (V.move x).firstMinimum` is the least length of a nonzero lattice vector at
the point `x`, cut off at `1`. Let `d ≥ 10` be at least the number `f` of infinite places,
`A ≥ 2 f (N + 1) + 2` and `A > 8 (N + 1)²` for `N = card n`. Then the function `ψ : r ↦ φ (r ⊕ 1)`
on the real group of `V` is integrable. The period against `F` of the series with centre `x ⊕ 1`
differs from the volume of `principalLevel n a` times `realConv ψ F x` by at most that volume times
`sliceConst A α ω * S * (10 / d)`. -/
lemma New.Exchange.norm_poincare_period_sub_le {E n : Type} {s : n → ℤˣ} [Field E] [CMType E]
    [Fintype n] [DecidableEq n] {V : Space E n s} [HasPrimitiveRoot5040 E]
    {F : G E s → ℂ} {S : ℝ} {a : NumberField.RingOfIntegers E} {R : ℝ} {A : ℕ} {d : ℝ}
    (hF : V.IsAutomorphic F) (hS : ∀ g : G E s, ‖F g‖ ≤ S) (ha : a ≠ 0)
    {l : NumberField.InfinitePlace E → HCParam (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (hF_level : HasLevel F (principalLevel n a))
    (hR_le : ∀ w : NumberField.InfinitePlace E, R ≤ ‖Φ w (a : E)‖)
    (hA : 2 * Core.numInfPlaces E * (card n + 1) + 2 ≤ A) (hA_sq : 8 * (card n + 1) ^ 2 < A)
    (h_gap : ∀ w : NumberField.InfinitePlace E, (l w).HasLargeGap (2 * A)) (hR_nonneg : 0 ≤ R)
    (x : G E s) (h_sep : d ^ 2 ≤ R * (V.move x).firstMinimum) (hd : Core.numInfPlaces E ≤ d)
    (hd_ten_le : 10 ≤ d) (ω α : GInf E (s ⊕ᵥ (1 : Unit → ℤˣ))) :
    Integrable (fun r : GInf E s ↦ translatedCoeff l α ω (inl s 1 ∘ r)) ∧
    ‖∫ h : G E s, ∑' γ : (V.sum (signedSpace (n := Unit) E 1)).Γ,
          poincareKernel (translatedCoeff l α ω) (principalLevel (n ⊕ Unit) a)
            ((inlLine E s x)⁻¹ * γ * inlLine E s h) * F h ∂V.quotMeasure -
        volume.real (principalLevel n a : Set (Gf E n)) •
          realConv (fun r : GInf E s ↦ translatedCoeff l α ω (inl s 1 ∘ r)) F x‖ ≤
      volume.real (principalLevel n a : Set (Gf E n)) * sliceConst A α ω * S * (10 / d) := by
  -- Unfold the period over the cosets `γ` of `V.Γ` in `Z.Γ`; only those that can meet the level
  -- condition contribute. The coset of `1` is the main term. The others are indexed by their last
  -- columns `col γ`, which are `d ^ 2`-separated, and the term of `γ` decays like `‖col γ‖⁻¹ ^ A`.
  set Z : Space E (n ⊕ Unit) (s ⊕ᵥ 1) := V.sum (signedSpace (n := Unit) E 1)
  set vol : ℝ := volume.real (principalLevel n a : Set (Gf E n))
  let transl (γ : Z.Γ) (h : G E s) : G E (s ⊕ᵥ 1) := (inlLine E s x)⁻¹ * γ.val * inlLine E s h
  let kernel (g : G E (s ⊕ᵥ 1)) : ℂ :=
    poincareKernel (translatedCoeff l α ω) (principalLevel (n ⊕ Unit) a) g
  let term (γ : Z.Γ) (h : G E s) : ℂ := kernel (transl γ h) * F h
  have slice_int (g : GInf E (s ⊕ᵥ 1)) :
      Integrable fun r : GInf E s ↦ translatedCoeff l α ω (g * inl s 1 ∘ r) :=
    (integrable_translatedCoeff_and_integral_norm_le hA_sq h_gap ω α g one_pos
      fun r ↦ (le_prod_opNorm fun w ↦ g w * inl s 1 (r w)).1).1
  refine ⟨by simpa only [one_mul] using slice_int 1, ?_⟩
  have d_pos : 0 < d := by linarith
  have S_nonneg : 0 ≤ S := (norm_nonneg _).trans (hS x)
  -- `reps` represents the cosets, `supp` those meeting the level condition, `base` is that of `1`
  obtain ⟨reps, hC, one_mem⟩ := ((inlLine E s).range.subgroupOf Z.Γ).exists_isComplement_left 1
  have : Countable reps := reps.to_countable.to_subtype
  let supp : Set reps := {γ : reps | ∃ k : G E s, (transl γ k).2 ∈ principalLevel (n ⊕ Unit) a}
  obtain ⟨k, hk⟩ :
      ∃ k : supp → G E s, ∀ γ : supp, (transl γ (k γ)).2 ∈ principalLevel (n ⊕ Unit) a :=
    Classical.skolem.1 fun γ : supp ↦ γ.property
  let base : supp := ⟨⟨1, one_mem⟩, x, by simp [transl]⟩
  -- `col γ`: the last column of `γ` in the Euclidean coordinates at `x ⊕ 1`
  obtain ⟨y, hy⟩ : ∃ y : Z.Γ → n ⊕ Unit → E, ∀ γ : Z.Γ, V.IsLastColumn γ (y γ) :=
    Classical.skolem.1 V.exists_isLastColumn
  let col (γ : supp) : EuclideanSpace ℂ (NumberField.InfinitePlace E × (n ⊕ Unit)) :=
    (Z.move (inlLine E s x)).archCoords (y γ)
  have separated : Pairwise fun γ γ' : supp ↦ d ^ 2 ≤ ‖col γ - col γ'‖ := by
    intro γ γ' h_ne
    -- if the columns agreed, `γ⁻¹ * γ'` would lie in the image of `inlLine E s`, so `γ = γ'`
    have y_ne : y γ ≠ y γ' := by
      intro y_eq
      have hγ' : V.IsLastColumn γ' (y γ) := by simpa only [y_eq] using hy γ'
      exact h_ne (Subtype.ext (hC.leftQuotientEquiv.symm.injective
        (QuotientGroup.eq.2 ((hy γ).inv_mul_mem_range hγ'))))
    rw [← map_sub]
    exact h_sep.trans
      ((hy γ).le_norm_archCoords_sub (hy γ') y_ne ha (hk γ) (hk γ') hR_nonneg hR_le)
  have norm_base_le : ‖col base‖ ≤ d := ((hy 1).norm_archCoords_one_le x).trans hd
  obtain ⟨summable, tsum_le⟩ : Summable (fun γ : Elem {base}ᶜ ↦ (d / ‖col γ‖) ^ A) ∧
      ∑' γ : Elem {base}ᶜ, (d / ‖col γ‖) ^ A ≤ 10 / d :=
    tsum_div_norm_pow_le_of_separated hd_ten_le separated norm_base_le
      (by simpa [← mul_assoc, finrank_real_of_complex])
  have kernel_int (γ : supp) : Integrable fun h : G E s ↦ kernel (transl γ h) :=
    (integral_norm_poincareKernel_le ha hA_sq h_gap ω α (hk γ) one_pos fun h ↦
      (le_prod_opNorm (transl γ h).1).1).1
  have term_int (γ : supp) : Integrable (term γ) :=
    (kernel_int γ).mul_bdd hF.1.aestronglyMeasurable (.of_forall hS)
  -- the decay: the product of the local operator norms of `transl γ h` is at least `‖col γ‖ / d`
  have term_le (γ : Elem {base}ᶜ) :
      ∫ h, ‖term γ h‖ ≤ vol * sliceConst A α ω * S * (d / ‖col γ‖) ^ A := by
    have col_pos : 0 < ‖col γ‖ := by
      nlinarith only [separated γ.property, norm_sub_le (col γ) (col base), norm_base_le, hd_ten_le]
    have norm_transl_ge (h : G E s) :
        ‖col γ‖ / d ≤ ∏ w, ‖((transl γ h).1 w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ := by
      have column_le : ‖col γ‖ ≤
          (∏ w, ‖((transl γ h).1 w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖) * Core.numInfPlaces E :=
        (hy γ).norm_archCoords_le x h
      grw [div_le_iff₀ d_pos, column_le, hd]
    have kernel_le : ∫ h, ‖kernel (transl γ h)‖ ≤ vol * sliceConst A α ω * (‖col γ‖ / d)⁻¹ ^ A :=
      (integral_norm_poincareKernel_le ha hA_sq h_gap ω α (hk γ) (div_pos col_pos d_pos)
        norm_transl_ge).2
    calc
      ∫ h, ‖term γ h‖ ≤ ∫ h, ‖kernel (transl γ h)‖ * S :=
        integral_mono (term_int γ).norm ((kernel_int γ).norm.mul_const S) fun h ↦ by
          grw [norm_mul, hS]
      _ ≤ vol * sliceConst A α ω * S * (d / ‖col γ‖) ^ A := by
        grw [integral_mul_const, kernel_le, inv_div, mul_right_comm]
  -- the sum over `Z.Γ` is a sum over cosets in `supp` and elements of `V.Γ`
  have tsum_eq (h : G E s) : ∑' γ : Z.Γ, term γ h = ∑' q : supp × V.Γ, term q.1 (q.2 * h) := by
    let p (g : G E (s ⊕ᵥ 1)) : ℂ := kernel ((inlLine E s x)⁻¹ * g * inlLine E s h) * F h
    have p_supp (σ : reps) (δ : G E s) (h_ne : p (σ * inlLine E s δ) ≠ 0) : σ ∈ supp := by
      have level : ((inlLine E s x)⁻¹ * (σ * inlLine E s δ) * inlLine E s h).2 ∈
          principalLevel (n ⊕ Unit) a :=
        mem_of_indicator_ne_zero (right_ne_zero_of_mul (left_ne_zero_of_mul h_ne))
      exact ⟨δ * h, by simpa [transl, mul_assoc] using level⟩
    have cosets : ∑' γ : Z.Γ, p γ = ∑' q : supp × V.Γ, p (q.1 * inlLine E s q.2) :=
      V.tsum_eq_tsum_cosets hC p_supp
    simpa [hF.2, p, term, transl, mul_assoc] using cosets
  -- unfolding over `V.Γ` turns the period into the sum of the integrals of `term γ` over the group
  have summable_norm : Summable fun γ : supp ↦ ∫ h, ‖term γ h‖ :=
    .compl_add (s := {base}) (.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      term_le (summable.mul_left _)) .of_finite
  have period : HasSum (fun γ : supp ↦ ∫ h, term γ h)
      (∫ h, ∑' γ : Z.Γ, term γ h ∂V.quotMeasure) := by
    simp_rw [tsum_eq]
    exact V.hasSum_integral_of_summable_integral_norm term_int summable_norm
  -- at `base`, translate by `x`: as `F` has level `a`, the integral is `vol` times the convolution
  have main_term : ∫ h, term base h =
      vol • realConv (fun r : GInf E s ↦ translatedCoeff l α ω (inl s 1 ∘ r)) F x := by
    have kernel_base (h : G E s) : kernel (transl base (x * h)) =
        translatedCoeff l α ω (inl s 1 ∘ h.1) * indicator (principalLevel n a) 1 h.2 := by
      simpa [kernel, transl, base] using
        poincareKernel_mul_inlLine (translatedCoeff l α ω) (g := 1) (Subgroup.one_mem _) h
    rw [← integral_mul_left_eq_self _ x, ← integral_mul_indicator_mul_eq_smul_realConv ha hF_level]
    simp only [term, kernel_base]
  have rest : HasSum (fun γ : Elem {base}ᶜ ↦ ∫ h, term γ h)
      (∫ h, ∑' γ : Z.Γ, term γ h ∂V.quotMeasure - ∫ h, term base h) :=
    (hasSum_singleton ..).hasSum_iff_compl.1 period
  have const_nonneg : 0 ≤ sliceConst A α ω := Finset.prod_nonneg fun w _ ↦ by positivity
  rw [← main_term]
  calc
    _ ≤ vol * sliceConst A α ω * S * ∑' γ : Elem {base}ᶜ, (d / ‖col γ‖) ^ A :=
      rest.norm_le_of_bounded (summable.hasSum.mul_left _)
        fun γ ↦ (norm_integral_le_integral_norm _).trans (term_le γ)
    _ ≤ vol * sliceConst A α ω * S * (10 / d) := by grw [tsum_le]

end DeepLevelPeriod
