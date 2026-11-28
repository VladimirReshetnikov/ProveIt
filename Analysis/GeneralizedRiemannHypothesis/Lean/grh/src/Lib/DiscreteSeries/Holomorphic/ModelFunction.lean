import Lib.DiscreteSeries.FlenstedJensen.SquareIntegrability

/-!
# The holomorphic model function and discrete series coefficients in the holomorphic chamber

For signs `ε` on the indices and weights `u τ`, the model function `New.holMinorsPi ε u` is a
product over τ of quotients of products of principal minors `New.weightMinors` with weights
`u τ + c τ` and `c τ`. Here `c τ` is a large constant on the indices of sign `1` and zero elsewhere.
In the main results the order `o` puts the signs `1` first and each weight `u τ` is K-dominant for
it. With the indices numbered `1, …, n` along `o` and `u τ (n + 1) = 0`, each quotient is then the
product of the leading minors of size `i` to the powers `u τ i - u τ (i + 1)`, and the model
function is holomorphic of weight `u` (`New.IsHolOfWeight`). Let `w` be a K-dominant weight that
jumps up by at least `γ > 500 n³ + A + n + 1` from the first block to the second, where `n` stands
for the number of indices and `A` is a given natural number. Then the discrete series coefficient of
the parameter `2 w + 2 ρ` (`New.twoRho`) is the model function `New.holMinors ε w`.

## Main definitions and results

* `New.isHolOfWeight_holMinorsPi`: `New.holMinorsPi ε u` is holomorphic of weight `u`.
* `New.IsHolOfWeight.circle_mean_holMinorsPi`: for `F` holomorphic of weight `u`, the mean over
  `|s| = 1` of `F (diag (s ^ o) * h)` divided by the character of weight `u` is
  `New.holMinorsPi ε u h * F 1`.
* `New.IsHolOfWeight.integral_mul_conj_holMinorsPi`: the reproducing formula
  `∫ F * conj m = (∫ |m|²) * F 1` for `m = New.holMinorsPi ε u`, if `F * conj m` is integrable.
* `New.IsHolOfWeight.eq_holMinorsPi_mul`: if `F g⁻¹ = conj (F g)`, then `F` is `F 1` times the model
  function.
* `New.dsCoeff_eq_holMinors`: for `w` as above, the parameter `2 w + 2 ρ` has gap `500 n³ + A`, and
  its coefficient `New.HCParam.dsCoeff` equals `New.holMinors ε w` on the unitary group. For the
  proof write a `g` near `1` as `x' * a * x` with `a` block diagonal and `x' - 1`, `x - 1` in the
  corner blocks; neither side sees `x'` and `x`, both agree at `a`, and both are analytic.

Notions from other files:
* `New.USign`: For a vector of signs ε, the unitary group U(J) of the diagonal matrix J = diag(ε).
* `New.IsHolOfWeight`: The function F on U(diag ε)^Φ extends analytically to products h b with b
  invertible and triangular for the order o, and the extension is the character of weight u at b
  times F(h). Optional signs ε' restrict h and b to block diagonal matrices; the default ε' = 1 is
  no restriction.
* `New.IsPosFirstOrder`, `New.IsKDominant`: The order o has distinct values and puts the signs +1
  first; the weight w satisfies w_j ≤ w_i whenever ε_i = ε_j and o_i < o_j.

## Relation to the literature

Known; see `Lib.DiscreteSeries.Holomorphic.HighestVectorExtension` for sources.
-/

namespace New

/-! ## Holomorphy of the model function, circle mean and reproducing formula -/

section HolomorphicMinor

open Finset DiscreteSeries Int MeasureTheory ComplexConjugate Complex Circle

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {o : n → ℤ} {Φ : Type}
  {F : (Φ → USign ε) → ℂ} [Fintype Φ] {u : Φ → n → ℤ}

/-- For the weight that is `a` on the indices of sign `1` and `b ≥ a` elsewhere, the quotient of
minors `New.holMinors` is `det ^ b` divided by the `(b - a)`-th power of the principal minor on
the indices of sign `1`. -/
theorem holMinors_ite_sign {a b : ℤ} (hab : a ≤ b) (g : USign ε) :
    holMinors ε (fun i : n ↦ if ε i = 1 then a else b) g =
      (g : Matrix n n ℂ).det ^ b / principalMinor g (fun i : n ↦ ε i = 1) ^ (b - a) := by
  -- Let `p` be the principal minor and `c` the shift in `holMinors`, whose denominator is `p ^ c`.
  -- Its numerator times `p ^ (b - a)` and `det ^ b * p ^ c` are both `weightMinors` of the weight
  -- `b + c` on the sign `1` and `b` elsewhere.
  let w (i : n) : ℤ := if ε i = 1 then a else b
  let c : ℤ := 2 * ∑ j : n, |w j|
  have hc_nonneg : 0 ≤ c := by positivity
  have h_top (i j : n) (hi : ε i = 1) (hj : ¬ε j = 1) :
      (w j + if ε j = 1 then c else 0) ≤ w i + if ε i = 1 then c else 0 := by
    grind [neg_sum_abs_le_and_le_sum_abs w i, neg_sum_abs_le_and_le_sum_abs w j]
  have h_weight : (fun i : n ↦ (w i + if ε i = 1 then c else 0) + if ε i = 1 then b - a else 0) =
      fun i : n ↦ b + if ε i = 1 then c else 0 := by grind
  have hg : (g : Matrix n n ℂ).det ≠ 0 := by simp [Matrix.GeneralLinearGroup.det_ne_zero]
  have h_num : weightMinors (fun i : n ↦ w i + if ε i = 1 then c else 0) (g : Matrix n n ℂ) *
      principalMinor g (fun i : n ↦ ε i = 1) ^ (b - a) =
        weightMinors (fun i : n ↦ b + if ε i = 1 then c else 0) g := by
    rw [← weightMinors_add_ite hg (sub_nonneg.2 hab) h_top, h_weight]
  have h_det : (g : Matrix n n ℂ).det ^ b *
      weightMinors (fun i : n ↦ if ε i = 1 then c else 0) g =
        weightMinors (fun i : n ↦ b + if ε i = 1 then c else 0) g := by
    rw [weightMinors_add_ite hg hc_nonneg (by simp), weightMinors_const hg,
      weightMinors_ite_eq_zpow hg hc_nonneg]
  have h_den_ne : weightMinors (fun i : n ↦ if ε i = 1 then c else 0) (g : Matrix n n ℂ) ≠ 0 := by
    simp [weightMinors_ite_eq_zpow hg hc_nonneg, zpow_ne_zero]
  rw [holMinors, div_eq_div_iff h_den_ne (by simp [zpow_ne_zero]), h_num, h_det]

@[simp]
theorem holMinorsPi_one : holMinorsPi ε u 1 = 1 := by simp [holMinorsPi, holMinors]

/-- `New.holMinorsPi ε u` is the quotient of the products over τ of the minors of weights
`u τ + c τ` and `c τ`, where `c τ` is `2 * ∑ j, |u τ j|` on the indices of sign `1` and zero
elsewhere. -/
theorem holMinorsPi_eq_div (u : Φ → n → ℤ) (h : Φ → USign ε) :
    let c (τ : Φ) (i : n) : ℤ := if ε i = 1 then 2 * ∑ j : n, |u τ j| else 0
    holMinorsPi ε u h =
      (∏ τ : Φ, weightMinors (u τ + c τ) (h τ)) / ∏ τ : Φ, weightMinors (c τ) (h τ) := by
  simp [holMinorsPi, holMinors, Pi.add_def]
/-- Left translation by `diag t`, with `|t i| = 1`, multiplies `New.holMinorsPi ε u` (a product of
quotients of principal minors of weights `u τ`) by the character of weight `u` at `t`. -/
theorem holMinorsPi_diagTorus_mul (t : n → Circle) (h : Φ → USign ε) :
    holMinorsPi ε u ((fun _ : Φ ↦ diagTorus ε t) * h) =
      (∏ τ : Φ, ∏ i : n, (t i : ℂ) ^ u τ i) * holMinorsPi ε u h := by
  have h_minors (w : n → ℤ) (g : USign ε) :
      weightMinors w ((diagTorus ε t * g : USign ε) : Matrix n n ℂ) =
        (∏ i : n, (t i : ℂ) ^ w i) * weightMinors w g := by
    simp [diagTorus, Matrix.GeneralLinearGroup.det_ne_zero]
  simp only [holMinorsPi, ← prod_mul_distrib]
  refine prod_congr rfl fun τ _ ↦ ?_
  -- the characters of the numerator and of the denominator differ by that of weight `u τ`
  let c (i : n) : ℤ := if ε i = 1 then 2 * ∑ j : n, |u τ j| else 0
  have h_char : ∏ i : n, (t i : ℂ) ^ (u τ i + c i) =
      (∏ i : n, (t i : ℂ) ^ u τ i) * ∏ i : n, (t i : ℂ) ^ c i := by
    simp [zpow_add₀, prod_mul_distrib]
  have h_ne : ∏ i : n, (t i : ℂ) ^ c i ≠ 0 := by simp [prod_ne_zero_iff, zpow_ne_zero]
  simp only [c] at h_char h_ne
  simp only [Pi.mul_apply, holMinors, h_minors, h_char]
  field_simp

omit [DecidableEq n] [Fintype Φ] in
/-- Let the order `o` be injective with the signs `1` first and each `u τ` be K-dominant, that is,
decrease weakly along `o` within the indices of each sign. Let `c` be `2 * ∑ j, |u τ j|` on the
indices of sign `1` and zero elsewhere. Then the weights `u τ + c` and `c` of the numerator and
the denominator of `New.holMinors` both decrease weakly along the whole order `o`. -/
theorem IsPosFirstOrder.isKDominant_shift (ho : IsPosFirstOrder ε o)
    (hu : ∀ τ : Φ, IsKDominant ε o (u τ)) (τ : Φ) :
    (IsKDominant 1 o fun i : n ↦ u τ i + if ε i = 1 then 2 * ∑ j : n, |u τ j| else 0) ∧
      IsKDominant 1 o fun i : n ↦ if ε i = 1 then 2 * ∑ j : n, |u τ j| else 0 := by
  -- Sign `1` comes first, so two indices in order lie in one block or go from `1` to `-1`.
  have h_signs {i j : n} (hij : o i < o j) : ε i = ε j ∨ ε i = 1 ∧ ε j = -1 := by
    grind [IsPosFirstOrder, units_eq_one_or (ε i), units_eq_one_or (ε j)]
  -- The shift is at least the difference of any two entries of `u τ`.
  have h_diff (i j : n) : u τ j ≤ u τ i + 2 * ∑ k : n, |u τ k| := by
    linarith [(neg_sum_abs_le_and_le_sum_abs (u τ) i).1, (neg_sum_abs_le_and_le_sum_abs (u τ) j).2]
  refine ⟨fun i j _ hij ↦ ?_, fun i j _ hij ↦ ?_⟩ <;> obtain h_same | ⟨hi, hj⟩ := h_signs hij
  · simpa [h_same] using hu τ i j h_same hij
  · simpa [hi, hj] using h_diff i j
  · simp [h_same]
  · simp [hi, hj, sum_nonneg]

open scoped Matrix.Norms.L2Operator in
/-- If the order o is injective with the indices of sign +1 first, and every u^τ is K-dominant
for o (decreases weakly within the indices of each sign), then `New.holMinorsPi ε u`, the product
of the quotients of principal minors of weights u^τ on U(diag ε)^Φ, is holomorphic of weight u:
it extends analytically with the character of weight u as factor under triangular matrices. -/
theorem isHolOfWeight_holMinorsPi (ho : IsPosFirstOrder ε o)
    (hu : ∀ τ : Φ, IsKDominant ε o (u τ)) : IsHolOfWeight ε o u (holMinorsPi ε u) := by
  -- `holMinorsPi` is a quotient of two products of minors with dominant weights `u + c` and `c`,
  -- where `c` is constant on the indices of sign `1` and zero elsewhere;
  -- `isHolOfWeight_weightMinors` gives analytic extensions `G₁` and `G₂` of the two.
  let c (τ : Φ) (i : n) : ℤ := if ε i = 1 then 2 * ∑ j : n, |u τ j| else 0
  obtain ⟨G₁, hG₁⟩ :
      IsHolOfWeight ε o (u + c) fun g ↦ ∏ τ : Φ, weightMinors (u τ + c τ) (g τ) := by
    simpa only [one_mul, c, Pi.add_def] using
      isHolOfWeight_weightMinors ho.1 1 (fun τ ↦ (ho.isKDominant_shift hu τ).1) (by simp)
  obtain ⟨G₂, hG₂⟩ : IsHolOfWeight ε o c fun g ↦ ∏ τ : Φ, weightMinors (c τ) (g τ) := by
    simpa only [one_mul] using
      isHolOfWeight_weightMinors ho.1 1 (fun τ ↦ (ho.isKDominant_shift hu τ).2) (by simp)
  refine ⟨G₁ / G₂, fun h b hb h_block ↦ ?_⟩
  let z (τ : Φ) : Matrix n n ℂ := h τ * b τ
  obtain ⟨h_an₁, h_eq₁⟩ : AnalyticAt ℂ G₁ z ∧
      G₁ z = (∏ τ : Φ, diagChar ((u + c) τ) (b τ)) * ∏ τ : Φ, weightMinors (u τ + c τ) (h τ) :=
    hG₁ h b hb h_block
  obtain ⟨h_an₂, h_eq₂⟩ : AnalyticAt ℂ G₂ z ∧
      G₂ z = (∏ τ : Φ, diagChar (c τ) (b τ)) * ∏ τ : Φ, weightMinors (c τ) (h τ) :=
    hG₂ h b hb h_block
  -- Both factors of the denominator `G₂ (h * b)` are nonzero.
  have h_char_ne : ∏ τ : Φ, diagChar (c τ) (b τ) ≠ 0 := by
    simp [diagChar, (hb _).diag_ne_zero ho.1, prod_ne_zero_iff, zpow_ne_zero]
  have h_minors_ne : ∏ τ : Φ, weightMinors (c τ) (h τ) ≠ 0 := by
    simp [c, Matrix.GeneralLinearGroup.det_ne_zero, sum_nonneg, weightMinors_ite_eq_zpow,
      prod_ne_zero_iff, zpow_ne_zero]
  -- The characters of weights `u + c` and `c` divide to the character of weight `u`.
  have h_char : ∏ τ : Φ, diagChar ((u + c) τ) (b τ) =
      (∏ τ : Φ, diagChar (u τ) (b τ)) * ∏ τ : Φ, diagChar (c τ) (b τ) := by
    simp [diagChar, (hb _).diag_ne_zero ho.1, prod_mul_distrib, zpow_add₀]
  refine ⟨h_an₁.div h_an₂ (h_eq₂.trans_ne (mul_ne_zero h_char_ne h_minors_ne)), ?_⟩
  have h_quot : holMinorsPi ε u h =
      (∏ τ : Φ, weightMinors (u τ + c τ) (h τ)) / ∏ τ : Φ, weightMinors (c τ) (h τ) :=
    holMinorsPi_eq_div u h
  rw [Pi.div_apply, h_eq₁, h_eq₂, h_char, h_quot]
  field_simp

/-- Let `o` put the signs `1` first, let each `u τ` be K-dominant for `o` (decreasing weakly within
the indices of each sign), and let `F` be holomorphic of weight `u` (`New.IsHolOfWeight`:
analytically extensible with the character of weight `u` as factor under triangular matrices).
Translate `h` on the left by the diagonal matrix with entries `s ^ o i` and divide `F` by the
character of weight `u`. The mean over `s` in the unit circle is `holMinorsPi ε u h * F 1`, where
`holMinorsPi` is the product of the quotients of principal minors of weights `u τ`. -/
theorem IsHolOfWeight.circle_mean_holMinorsPi (ho : IsPosFirstOrder ε o)
    (hu : ∀ τ : Φ, IsKDominant ε o (u τ)) (hF : IsHolOfWeight ε o u F) (h : Φ → USign ε) :
    ∫ θ : UnitAddCircle, F ((fun _ : Φ ↦ diagTorus ε fun i : n ↦ θ.toCircle ^ o i) * h) *
        ∏ τ : Φ, ∏ i : n, ((((θ.toCircle ^ o i) ^ u τ i)⁻¹ : Circle) : ℂ) =
      holMinorsPi ε u h * F 1 := by
  -- Multiply `F` by the denominator of `holMinorsPi`, of weight `c`: the product has the weight
  -- `u + c`, dominant for the whole order, so `IsHolOfWeight.circle_mean_weightMinors` applies.
  let c (τ : Φ) (i : n) : ℤ := if ε i = 1 then 2 * ∑ j : n, |u τ j| else 0
  have h_den : IsHolOfWeight ε o c fun g ↦ ∏ τ : Φ, weightMinors (c τ) (g τ) := by
    simpa only [one_mul] using
      isHolOfWeight_weightMinors ho.1 1 (fun τ ↦ (ho.isKDominant_shift hu τ).2) (by simp)
  have h_dom (τ : Φ) : IsKDominant 1 o ((u + c) τ) := (ho.isKDominant_shift hu τ).1
  let r (θ : UnitAddCircle) : Φ → USign ε := fun _ ↦ diagTorus ε fun i : n ↦ θ.toCircle ^ o i
  let χ (w : Φ → n → ℤ) (θ : UnitAddCircle) : ℂ := ∏ τ, ∏ i, ((θ.toCircle : ℂ) ^ o i) ^ w τ i
  have h_mean : ∫ θ : UnitAddCircle,
      F (r θ * h) * (∏ τ : Φ, weightMinors (c τ) ((r θ * h) τ)) * (χ (u + c) θ)⁻¹ =
        (∏ τ : Φ, weightMinors (u τ + c τ) (h τ)) * F 1 := by
    -- `circle_mean_weightMinors` allows a block restriction `ε'` and an analytic factor `q`;
    -- it is applied to `F` times the denominator with both of these equal to `1`.
    simpa [r, χ, Pi.add_def, Pi.mul_def] using
      (hF.mul ho.1 h_den).circle_mean_weightMinors (g := h) ho.1 (.inl rfl) h_dom (by simp) 1
        analyticOnNhd_const
  -- Under rotation the denominator changes by its own character, which cancels.
  have h_rot (θ : UnitAddCircle) : ∏ τ : Φ, weightMinors (c τ) ((r θ * h) τ) =
      χ c θ * ∏ τ : Φ, weightMinors (c τ) (h τ) := by
    simp [r, χ, prod_mul_distrib, diagTorus, Matrix.GeneralLinearGroup.det_ne_zero, zpow_ne_zero]
  have h_cancel (θ : UnitAddCircle) : χ c θ * (χ (u + c) θ)⁻¹ = (χ u θ)⁻¹ := by
    have h_ne : χ c θ ≠ 0 := by simp [χ, prod_ne_zero_iff, zpow_ne_zero]
    rw [show χ (u + c) θ = χ u θ * χ c θ by simp [χ, prod_mul_distrib, zpow_ne_zero, zpow_add₀]]
    field_simp
  have h_minors_ne : ∏ τ : Φ, weightMinors (c τ) (h τ) ≠ 0 := by
    simp [c, Matrix.GeneralLinearGroup.det_ne_zero, sum_nonneg, weightMinors_ite_eq_zpow,
      prod_ne_zero_iff, zpow_ne_zero]
  have h_quot : holMinorsPi ε u h =
      (∏ τ : Φ, weightMinors (u τ + c τ) (h τ)) / ∏ τ : Φ, weightMinors (c τ) (h τ) :=
    holMinorsPi_eq_div u h
  rw [h_quot, div_mul_eq_mul_div, eq_div_iff h_minors_ne, ← h_mean, ← integral_mul_const]
  refine integral_congr_ae (.of_forall fun θ ↦ ?_)
  have h_coe : ∏ τ : Φ, ∏ i : n, ((((θ.toCircle ^ o i) ^ u τ i)⁻¹ : Circle) : ℂ) = (χ u θ)⁻¹ := by
    simp [χ]
  simp only [h_rot, h_coe, ← h_cancel]
  ring

/-- The reproducing formula. Let `o` put the signs `1` first, let each `u τ` be K-dominant for `o`
(decreasing weakly within the indices of each sign), and let `F` be holomorphic of weight `u` on
U(diag ε)^Φ (analytically extensible with the character of weight `u` under triangular matrices).
If `F * conj m` is integrable for the invariant measure, where `m = holMinorsPi ε u` is the
product of quotients of principal minors of weight `u`, then its integral is `F 1` times the
integral of `|m|²`. -/
theorem IsHolOfWeight.integral_mul_conj_holMinorsPi (ho : IsPosFirstOrder ε o)
    (hu : ∀ τ : Φ, IsKDominant ε o (u τ)) (hF : IsHolOfWeight ε o u F)
    (hi : Integrable fun h : Φ → USign ε ↦ F h * conj (holMinorsPi ε u h)) :
    ∫ h : Φ → USign ε, F h * conj (holMinorsPi ε u h) =
      (∫ h : Φ → USign ε, ‖holMinorsPi ε u h‖ ^ 2 : ℝ) * F 1 := by
  -- Average the integrand over the rotations, which preserve the measure. Under them `holMinorsPi`
  -- moves by a character, whose conjugate is the factor in `circle_mean_holMinorsPi`.
  rw [← integral_complex_ofReal, ← integral_mul_const]
  let r (θ : UnitAddCircle) : Φ → USign ε := fun _ ↦ diagTorus ε fun i : n ↦ θ.toCircle ^ o i
  refine integral_eq_of_circle_mean (T := fun θ h ↦ r θ * h) (Continuous.measurable (by fun_prop))
    (fun θ ↦ measurePreserving_mul_left _ (r θ)) hi fun h ↦ ?_
  have h_rot (t : n → Circle) : conj (holMinorsPi ε u ((fun _ : Φ ↦ diagTorus ε t) * h)) =
      (∏ τ : Φ, ∏ i : n, (((t i ^ u τ i)⁻¹ : Circle) : ℂ)) * conj (holMinorsPi ε u h) := by
    simp [holMinorsPi_diagTorus_mul, ← coe_inv_eq_conj]
  calc ∫ θ : UnitAddCircle, F (r θ * h) * conj (holMinorsPi ε u (r θ * h))
      = (∫ θ : UnitAddCircle, F (r θ * h) *
          ∏ τ : Φ, ∏ i : n, ((((θ.toCircle ^ o i) ^ u τ i)⁻¹ : Circle) : ℂ)) *
            conj (holMinorsPi ε u h) := by
        simp only [r, h_rot, ← mul_assoc, integral_mul_const]
    _ = holMinorsPi ε u h * F 1 * conj (holMinorsPi ε u h) := by
        rw [hF.circle_mean_holMinorsPi ho hu]
    _ = ((‖holMinorsPi ε u h‖ ^ 2 : ℝ) : ℂ) * F 1 := by
        rw [mul_right_comm, mul_conj', ofReal_pow]

/-- Let the order `o` be injective with signs `1` first, each `u τ` K-dominant (decreasing weakly
within the indices of each sign), and `F` holomorphic of weight `u` on U(diag ε)^Φ (analytically
extensible with the character of weight `u` under triangular matrices) with `F g⁻¹ = conj (F g)`.
Then `F` is `F 1` times `New.holMinorsPi ε u`, the product of quotients of principal minors. -/
theorem IsHolOfWeight.eq_holMinorsPi_mul (ho : IsPosFirstOrder ε o)
    (hu : ∀ τ : Φ, IsKDominant ε o (u τ)) (hF : IsHolOfWeight ε o u F)
    (hF_inv : ∀ g : Φ → USign ε, F g⁻¹ = conj (F g))
    (h : Φ → USign ε) : F h = holMinorsPi ε u h * F 1 := by
  -- conjugating the law for right translation by the torus gives the law for left translation
  have h_left (t : n → Circle) (y : Φ → USign ε) :
      F ((fun _ ↦ diagTorus ε t)⁻¹ * y) =
        (∏ τ : Φ, ∏ i : n, (((t i ^ u τ i)⁻¹ : Circle) : ℂ)) * F y := by
    simpa [← hF_inv, ← coe_inv_eq_conj, ← coe_zpow] using
      congrArg conj (hF.apply_mul_diagTorus y⁻¹ t)
  -- so the integrand of the circle mean is the constant `F h`
  have h_const (t : n → Circle) :
      F ((fun _ ↦ diagTorus ε t) * h) * ∏ τ : Φ, ∏ i : n, (((t i ^ u τ i)⁻¹ : Circle) : ℂ) =
        F h := by
    rw [mul_comm, ← h_left, inv_mul_cancel_left]
  calc F h = ∫ _ : UnitAddCircle, F h := by simp [Measure.real]
    _ = ∫ θ : UnitAddCircle, F ((fun _ : Φ ↦ diagTorus ε fun i : n ↦ θ.toCircle ^ o i) * h) *
          ∏ τ : Φ, ∏ i : n, ((((θ.toCircle ^ o i) ^ u τ i)⁻¹ : Circle) : ℂ) := by
        simp only [h_const]
    _ = holMinorsPi ε u h * F 1 := hF.circle_mean_holMinorsPi ho hu h

end HolomorphicMinor

/-!
## Discrete series coefficients in the holomorphic chamber

Parameters are doubled, `l = 2 λ`.
-/

section HolomorphicChamber

open Matrix Finset Fintype Int Filter Topology ComplexOrder DiscreteSeries

section

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {o : n → ℤ}

/-! ### Matrices in a corner block -/

/-- The matrix `y` lies in the corner block with rows of sign `s` and columns of sign `-s`: all
other entries vanish. If the signs `1` come first, this is the upper right block for `s = 1` and the
lower left block for `s = -1`. -/
def IsInCornerBlock (ε : n → ℤˣ) (s : ℤˣ) (y : Matrix n n ℂ) : Prop :=
  ∀ i j : n, ¬(ε i = s ∧ ε j = -s) → y i j = 0

/-- A corner block is stable under multiplication by block diagonal matrices on both sides. -/
theorem IsInCornerBlock.mul_mul {s : ℤˣ} {y p q : Matrix n n ℂ} (hy : IsInCornerBlock ε s y)
    (hp : p ∈ blockDiagAlg ε) (hq : q ∈ blockDiagAlg ε) : IsInCornerBlock ε s (p * y * q) := by
  intro i j hij
  have h_term (a b : n) : p i a * y a b * q b j = 0 := by
    by_cases h_row : ε i = ε a
    · by_cases h_col : ε b = ε j
      · simp [hy a b (by rwa [← h_row, h_col])]
      · simp [mem_blockDiagAlg.1 hq b j h_col]
    · simp [mem_blockDiagAlg.1 hp i a h_row]
  simp only [mul_apply, sum_mul, h_term, sum_const_zero]

/-- If `x - 1` lies in a corner block, then so does `kᴴ * x * k - 1` for `k` in
`K = U(diag ε) ∩ U(n)`. -/
theorem IsInCornerBlock.conj_sub_one {s : ℤˣ} {x : Matrix n n ℂ}
    (hx : IsInCornerBlock ε s (x - 1)) (k : maxCompactU ε) :
    IsInCornerBlock ε s ((k : Matrix n n ℂ)ᴴ * x * k - 1) := by
  have hk_mem : (k : Matrix n n ℂ) ∈ blockDiagAlg ε := mem_maxCompactU.1 k.property
  have h_conj : (k : Matrix n n ℂ)ᴴ * x * k - 1 = (k : Matrix n n ℂ)⁻¹ * (x - 1) * k := by
    simp [mul_sub, sub_mul, ← maxCompactU.coe_inv, GeneralLinearGroup.det_ne_zero]
  simpa only [h_conj] using hx.mul_mul (blockDiagAlg.inv_mem hk_mem) hk_mem

/-- Let `x - 1` lie in the corner block with rows of sign `s`, and let the injective order `o` put
the signs `s` before the signs `-s`. Then `x` is upper unipotent for `o`: it is invertible and upper
triangular (`New.IsBorelMatrix`), and every character `diagChar w x = ∏ i, x i i ^ w i` of the
diagonal is `1`. -/
theorem IsInCornerBlock.isBorelMatrix_and_diagChar_eq_one {s : ℤˣ} {x : Matrix n n ℂ}
    (hx : IsInCornerBlock ε s (x - 1)) (ho : o.Injective)
    (h_first : ∀ i j : n, ε i = s → ε j = -s → o i < o j) :
    IsBorelMatrix o x ∧ ∀ w : n → ℤ, diagChar w x = 1 := by
  have h_diag (i : n) : x i i = 1 := by
    simpa [sub_eq_zero] using hx i i fun ⟨hi, hj⟩ ↦ (h_first i i hi hj).false
  have h_tri : x.BlockTriangular o := fun i j hij ↦ by
    have h_ne : i ≠ j := fun h_eq ↦ hij.ne (congrArg o h_eq.symm)
    simpa [h_ne] using hx i j fun ⟨hi, hj⟩ ↦ (h_first i j hi hj).not_gt hij
  exact ⟨⟨h_tri, by simp [det_eq_prod_diag_of_blockTriangular ho h_tri, h_diag]⟩,
    fun w ↦ by simp [diagChar, h_diag]⟩

/-- A block diagonal matrix that is invertible and upper triangular for the order `o`
(`New.IsBorelMatrix`) is so for every order `o'` whose strict inequalities inside the blocks hold
for `o` too. -/
theorem IsBorelMatrix.of_mem_blockDiagAlg {o' : n → ℤ} {b : Matrix n n ℂ} (hb : IsBorelMatrix o b)
    (hb_mem : b ∈ blockDiagAlg ε) (h_order : ∀ i j : n, ε i = ε j → o' j < o' i → o j < o i) :
    IsBorelMatrix o' b := by
  refine ⟨fun i j hij ↦ ?_, hb.2⟩
  by_cases h_sign : ε i = ε j
  · exact hb.1 (h_order i j h_sign hij)
  · exact mem_blockDiagAlg.1 hb_mem i j h_sign

/-! ### Factorisations near the identity -/

open Norms.L2Operator in
/-- Each block diagonal matrix `y` near `1` is `(1 + z) * b`, where `z` is block diagonal and
strictly lower triangular for the order `o`, and `b` is block diagonal, invertible and upper
triangular. Both factors lie in a given neighbourhood `P` of `1`. The order `o` may have ties. -/
theorem eventually_exists_eq_lower_mul_borel (ε : n → ℤˣ) (o : n → ℤ)
    {P : Set (Matrix n n ℂ)} (hP : P ∈ 𝓝 1) :
    ∀ᶠ y : Matrix n n ℂ in 𝓝 1, y ∈ blockDiagAlg ε → ∃ z b : Matrix n n ℂ,
      (∀ i j : n, ¬(o j < o i ∧ ε i = ε j) → z i j = 0) ∧
      b ∈ blockDiagAlg ε ∧
      IsBorelMatrix o b ∧
      1 + z ∈ P ∧
      b ∈ P ∧
      y = (1 + z) * b := by
  let L : Matrix n n ℂ →L[ℝ] Matrix n n ℂ := (lowerMask ε o).restrictScalars ℝ
  have h_supp (Z : Matrix n n ℂ) (i j : n) (hij : ¬(o j < o i ∧ ε i = ε j)) : L Z i j = 0 := by
    simp [L, hij]
  have h_mem (Z : Matrix n n ℂ) : 1 + L Z ∈ blockDiagAlg ε :=
    add_mem (one_mem _) (mem_blockDiagAlg.2 fun i j h_sign ↦ h_supp Z i j fun h ↦ h_sign h.2)
  have h_idem (Z : Matrix n n ℂ) : lowerMask ε o (L Z) = lowerMask ε o Z := by
    ext i j
    simp +contextual [L]
  -- The chart `ψ` at `1` of `exists_borel_chart` for the map `Z ↦ 1 + Z`: it is differentiable at
  -- `1`, takes the value `0` there, and gives the factorisation recorded at the end of the proof.
  obtain ⟨ψ, ⟨hψ_deriv, hψ_one⟩, h_chart⟩ :=
    exists_borel_chart ε o L (.const_add 1 (hasStrictFDerivAt_id 0)) (add_zero 1) h_mem h_idem
  have h_near (M : Matrix n n ℂ →L[ℝ] Matrix n n ℂ) :
      ∀ᶠ y : Matrix n n ℂ in 𝓝 1, 1 + M (ψ y) ∈ P :=
    (continuousAt_const.add
      (M.continuous.continuousAt.comp hψ_deriv.continuousAt)).preimage_mem_nhds
        (by simpa [hψ_one] using hP)
  filter_upwards [h_chart, h_near L, h_near (1 - L)] with y hy h_lower h_upper hy_mem
  obtain ⟨hb, ⟨-, hb_mem⟩, hy_eq⟩ : IsBorelMatrix o (1 + (1 - L) (ψ y)) ∧
      (1 + L (ψ y) ∈ blockDiagAlg ε ∧ 1 + (1 - L) (ψ y) ∈ blockDiagAlg ε) ∧
      y = (1 + L (ψ y)) * (1 + (1 - L) (ψ y)) := hy hy_mem
  exact ⟨L (ψ y), 1 + (1 - L) (ψ y), h_supp (ψ y), hb_mem, hb, h_lower, h_upper, hy_eq⟩

/-- Each matrix `g` near `1` is `x' * a * x` with `a` block diagonal and in a given neighbourhood
`P` of `1`, with `x - 1` in the upper right block (rows of sign `1`, columns of sign `-1`) and
`x' - 1` in the lower left block. -/
theorem eventually_exists_eq_corner_mul_mul_corner (ε : n → ℤˣ) {P : Set (Matrix n n ℂ)}
    (hP : P ∈ 𝓝 1) :
    ∀ᶠ g : Matrix n n ℂ in 𝓝 1, ∃ x' a x : Matrix n n ℂ,
      IsInCornerBlock ε (-1) (x' - 1) ∧
      a ∈ blockDiagAlg ε ∧
      a ∈ P ∧
      IsInCornerBlock ε 1 (x - 1) ∧
      g = x' * a * x := by
  -- Factor `g = (1 + z) * b` for the two-level order `-ε` (for the constant signs `1` every matrix
  -- is block diagonal). Take `a` the block diagonal part of `b`, `x' = 1 + z` and `x = a⁻¹ * b`.
  have h_part : ∀ᶠ b : Matrix n n ℂ in 𝓝 1,
      blockDiagPart ε b ∈ P ∧ (blockDiagPart ε b).det ≠ 0 :=
    (blockDiagPart ε).continuous.tendsto' 1 1 (blockDiagPart_of_mem (one_mem _))
      (Eventually.and hP (ContinuousAt.eventually_ne (by fun_prop) (by simp)))
  filter_upwards [eventually_exists_eq_lower_mul_borel 1 (fun i ↦ -(ε i : ℤ)) h_part] with g hg
  obtain ⟨z, b, hz, -, hb, -, ⟨ha_near, ha_det⟩, rfl⟩ := hg mem_blockDiagAlg_one
  set a : Matrix n n ℂ := blockDiagPart ε b with ha
  have ha_mem : a ∈ blockDiagAlg ε := blockDiagPart_mem b
  have h_level (s t : ℤˣ) : -(t : ℤ) < -(s : ℤ) ↔ s = -1 ∧ t = 1 := by
    rcases units_eq_one_or s with rfl | rfl <;> rcases units_eq_one_or t with rfl | rfl <;> simp
  have h_lower : IsInCornerBlock ε (-1) z :=
    fun i j hij ↦ hz i j fun h_below ↦ hij ((h_level (ε i) (ε j)).1 h_below.1)
  have h_upper : IsInCornerBlock ε 1 (b - a) := by
    intro i j hij
    by_cases h_sign : ε i = ε j
    · simp [ha, blockDiagPart, h_sign]
    · -- Entries off the blocks and outside the upper right one lie in the lower left one.
      have h_signs : ε i = -1 ∧ ε j = 1 := by
        grind [units_eq_one_or (ε i), units_eq_one_or (ε j)]
      simp [ha, blockDiagPart, h_sign, hb.1 ((h_level (ε i) (ε j)).2 h_signs)]
  have h_sub : a⁻¹ * b - 1 = a⁻¹ * (b - a) * 1 := by
    rw [mul_one, mul_sub, nonsing_inv_mul a ha_det.isUnit]
  refine ⟨1 + z, a, a⁻¹ * b, by rwa [add_sub_cancel_left], ha_mem, ha_near, ?_,
    by rw [mul_assoc, mul_nonsing_inv_cancel_left a b ha_det.isUnit]⟩
  rw [h_sub]
  exact h_upper.mul_mul (blockDiagAlg.inv_mem ha_mem) (one_mem _)

/-- For a weight that decreases weakly along the injective order `o`, multiplying by an invertible
lower triangular `b'` on the left and an upper triangular `b` on the right multiplies
`weightMinors v` (the product of the leading minors of size `i` along `o` to the powers
`v i - v (i + 1)`, with `v (n + 1) = 0`) by the characters of the two diagonals. -/
theorem IsKDominant.weightMinors_mul_mul_of_isBorelMatrix {v : n → ℤ} (ho : o.Injective)
    (hv : IsKDominant 1 o v) {b' y b : Matrix n n ℂ} (hb' : IsBorelMatrix (-o) b')
    (hy : y.det ≠ 0) (hb : IsBorelMatrix o b) :
    weightMinors v (b' * y * b) = diagChar v b' * diagChar v b * weightMinors v y := by
  rw [hv.weightMinors_mul_borel ho ((det_mul b' y).trans_ne (mul_ne_zero hb'.2 hy))
      mem_blockDiagAlg_one hb,
    hv.weightMinors_oppBorel_mul ho hy mem_blockDiagAlg_one hb', mul_right_comm]

/-! ### The model function -/

/-- Let the order `o` put the signs `1` first and let `w` decrease weakly within each block. For
invertible `b'`, `y`, `b` with `b'` lower and `b` upper triangular for `o`, the model function
`holMinors ε w` at `b' * y * b` is its value at `y` times `∏ i, b' i i ^ w i` and
`∏ i, b i i ^ w i`. -/
theorem holMinors_oppBorel_mul_mul_borel (ho : IsPosFirstOrder ε o) {w : n → ℤ}
    (hw : IsKDominant ε o w) {b' y b : Matrix n n ℂ} (hb' : IsBorelMatrix (-o) b')
    (hy : y.det ≠ 0) (hb : IsBorelMatrix o b) :
    holMinors ε w (b' * y * b) = diagChar w b' * diagChar w b * holMinors ε w y := by
  -- Numerator and denominator obey this rule, with the weights `w + c` and `c`.
  let c (i : n) : ℤ := if ε i = 1 then 2 * ∑ j : n, |w j| else 0
  obtain ⟨h_num, h_den⟩ : IsKDominant 1 o (fun i ↦ w i + c i) ∧ IsKDominant 1 o c :=
    ho.isKDominant_shift (u := fun _ : Unit ↦ w) (fun _ ↦ hw) ()
  have h_add {z : Matrix n n ℂ} (hz : ∀ i : n, z i i ≠ 0) :
      diagChar (fun i ↦ w i + c i) z = diagChar w z * diagChar c z := by
    simp [diagChar, zpow_add₀, hz, prod_mul_distrib]
  have h_ne {z : Matrix n n ℂ} (hz : ∀ i : n, z i i ≠ 0) : diagChar c z ≠ 0 :=
    prod_ne_zero_iff.2 fun i _ ↦ zpow_ne_zero _ (hz i)
  have hb'_diag : ∀ i : n, b' i i ≠ 0 := hb'.diag_ne_zero (neg_injective.comp ho.1)
  have hb_diag : ∀ i : n, b i i ≠ 0 := hb.diag_ne_zero ho.1
  change weightMinors (fun i ↦ w i + c i) (b' * y * b) / weightMinors c (b' * y * b) =
    diagChar w b' * diagChar w b * (weightMinors (fun i ↦ w i + c i) y / weightMinors c y)
  rw [h_num.weightMinors_mul_mul_of_isBorelMatrix ho.1 hb' hy hb,
    h_den.weightMinors_mul_mul_of_isBorelMatrix ho.1 hb' hy hb, h_add hb'_diag, h_add hb_diag]
  field_simp [h_ne hb'_diag, h_ne hb_diag]

open Norms.L2Operator in
/-- With `c = 2 * ∑ j, |w j|` on the indices of sign `1` and zero elsewhere, `holMinors ε w` is the
quotient of the products of principal minors of weights `w + c` and `c`. It is analytic at each
point of `U(diag ε)`, for every weight `w`. -/
theorem analyticAt_holMinors (w : n → ℤ) (g : USign ε) : AnalyticAt ℂ (holMinors ε w) g := by
  -- The denominator is a power of the principal minor on the signs `1`, nonzero on the group.
  have hg : (g : Matrix n n ℂ).det ≠ 0 := GeneralLinearGroup.det_ne_zero _
  refine (analyticAt_weightMinors hg).div (analyticAt_weightMinors hg) ?_
  rw [weightMinors_ite_eq_zpow hg (by positivity)]
  exact zpow_ne_zero _ (U.principalMinor_sign_ne_zero 1 g)

open Norms.L2Operator in
/-- Let `f` and `f'` be functions of a matrix that are analytic at each point of `U(diag ε)`. If
they agree on a neighbourhood of `1` in the group, they agree on the whole group. -/
theorem USign.eq_of_analyticAt_of_eventually_eq {f f' : Matrix n n ℂ → ℂ}
    (hf : ∀ g : USign ε, AnalyticAt ℂ f g) (hf' : ∀ g : USign ε, AnalyticAt ℂ f' g)
    (h_near : ∀ᶠ g : USign ε in 𝓝 1, f g = f' g) (g : USign ε) : f g = f' g := by
  -- Restrict both functions to an analytic path from `1` to `g`.
  obtain ⟨c, hc_zero, rfl, hc, -⟩ : ∃ c : ℝ → USign ε, c 0 = 1 ∧ c 1 = g ∧
      (∀ t : ℝ, AnalyticAt ℝ (fun s : ℝ ↦ (c s : Matrix n n ℂ)) t) ∧
      ∀ t : ℝ, (c t : Matrix n n ℂ) ∈ blockDiagAlg 1 :=
    exists_analytic_path (ε' := 1) (.inl rfl) g mem_blockDiagAlg_one
  have hc_cont : Continuous c :=
    continuous_U_iff_matrix.2 (continuous_iff_continuousAt.2 fun t ↦ (hc t).continuousAt)
  have h_comp {q : Matrix n n ℂ → ℂ} (hq : ∀ g : USign ε, AnalyticAt ℂ q g) :
      AnalyticOnNhd ℝ (fun t : ℝ ↦ q (c t)) Set.univ :=
    fun t _ ↦ (hq (c t)).restrictScalars.comp_of_eq (hc t) rfl
  have h_path : (fun t : ℝ ↦ f (c t)) = fun t : ℝ ↦ f' (c t) :=
    (h_comp hf).eq_of_eventuallyEq (h_comp hf') ((hc_cont.tendsto' 0 1 hc_zero).eventually h_near)
  exact congrFun h_path 1

/-! ### The coefficient in the holomorphic chamber -/

variable {l : HCParam ε} {h : ℕ}

omit [DecidableEq n] in
/-- If the parameter `l`, of some gap `h` (its entries are distinct, of the parity of `n - 1`, and
those of `l / 2` at opposite signs are at least `h` apart), decreases along the order `o` within
each block of equal signs, then the highest weight `l.lowestKType` of its lowest `K`-type decreases
weakly along `o` in each block. -/
theorem HCParam.HasGap.isKDominant_lowestKType_of_order (hl : l.HasGap h)
    (h_same : ∀ i j : n, ε i = ε j → o i < o j → l j < l i) : IsKDominant ε o l.lowestKType :=
  fun i j h_sign hij ↦ hl.isKDominant_lowestKType i j h_sign (neg_lt_neg (h_same i j h_sign hij))

/-- Let `l` be a parameter of some gap `h` (in particular with distinct entries) whose entries at
the signs `1` lie below those at the signs `-1`. Let `a` be invertible, `x' - 1` in the lower left
and `x - 1` in the upper right block. Then Flensted-Jensen's integral `l.flenstedJensen 1` (an
integral over `k` in `K` whose integrand has denominator
`weightMinors (-paramAddRho l) (kᴴ * g * k)`), based at the identity, has the same value at
`x' * a * x` and at `a`. -/
theorem flenstedJensen_corner_mul_mul_corner (hl : l.HasGap h)
    (h_cross : ∀ i j : n, ε i = 1 → ε j = -1 → l i < l j) {x' a x : Matrix n n ℂ}
    (hx' : IsInCornerBlock ε (-1) (x' - 1)) (ha : a.det ≠ 0) (hx : IsInCornerBlock ε 1 (x - 1)) :
    l.flenstedJensen 1 (x' * a * x) = l.flenstedJensen 1 a := by
  -- In the order of decreasing `l` the signs `-1` come first, so the conjugates of `x'` by `K` are
  -- upper and those of `x` are lower unipotent. They do not change the denominator of the
  -- integrand, a product of minors of weight `-(λ + ρ)`, which increases in that order.
  have h_dom : IsKDominant 1 l (-paramAddRho l) := hl.isKDominant_neg_paramAddRho
  have h_denom (k : maxCompactU ε) :
      weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * (x' * a * x) * k) =
        weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * a * k) := by
    obtain ⟨h_left, h_left_char⟩ : IsBorelMatrix (-l) ((k : Matrix n n ℂ)ᴴ * x' * k) ∧
        ∀ w : n → ℤ, diagChar w ((k : Matrix n n ℂ)ᴴ * x' * k) = 1 :=
      (hx'.conj_sub_one k).isBorelMatrix_and_diagChar_eq_one hl.neg.injective
        fun i j hi hj ↦ neg_lt_neg (h_cross j i hj hi)
    obtain ⟨h_right, h_right_char⟩ : IsBorelMatrix l ((k : Matrix n n ℂ)ᴴ * x * k) ∧
        ∀ w : n → ℤ, diagChar w ((k : Matrix n n ℂ)ᴴ * x * k) = 1 :=
      (hx.conj_sub_one k).isBorelMatrix_and_diagChar_eq_one hl.injective h_cross
    have h_split : (k : Matrix n n ℂ)ᴴ * (x' * a * x) * k =
        (k : Matrix n n ℂ)ᴴ * x' * k * ((k : Matrix n n ℂ)ᴴ * a * k) *
          ((k : Matrix n n ℂ)ᴴ * x * k) := by
      simp [← maxCompactU.coe_inv, mul_assoc]
    rw [h_split, h_dom.weightMinors_mul_mul_of_isBorelMatrix hl.injective h_left
      (by simp [ha, GeneralLinearGroup.det_ne_zero]) h_right, h_left_char, h_right_char,
      one_mul, one_mul]
  simp only [flenstedJensen, h_denom]

/-- Let the order `o` put the signs `1` first, and let the parameter `l` decrease along `o` within
each block. It has some gap `h`: its entries are distinct, of the parity of `n - 1`, and those of
`l / 2` at opposite signs are at least `h` apart. On block diagonal matrices `a` near `1`,
Flensted-Jensen's integral `l.flenstedJensen 1 a` (based at the identity; an integral over `k` in
`K` with denominator `weightMinors (-paramAddRho l) (kᴴ * a * k)`) is the model function
`holMinors`, a quotient of products of principal minors, for the highest weight `l.lowestKType` of
the lowest `K`-type. -/
theorem eventually_flenstedJensen_eq_holMinors_of_mem_blockDiagAlg (hl : l.HasGap h)
    (ho : IsPosFirstOrder ε o) (h_same : ∀ i j : n, ε i = ε j → o i < o j → l j < l i) :
    ∀ᶠ a : Matrix n n ℂ in 𝓝 1,
      a ∈ blockDiagAlg ε → l.flenstedJensen 1 a = holMinors ε l.lowestKType a := by
  -- Write `a = b' * b` with `b' = 1 + z` lower and `b` upper triangular, both block diagonal. Such
  -- factors multiply both sides by the same characters, and both sides are `1` at `1`.
  have h_acc : {z : Matrix n n ℂ | z.IsAccretive} ∈ 𝓝 1 := PosDef.one.isAccretive.setOf_mem_nhds
  have h_dom : IsKDominant ε o l.lowestKType := hl.isKDominant_lowestKType_of_order h_same
  have h_order {i j : n} (h_sign : ε i = ε j) (hij : l j < l i) : o i < o j := by
    grind [ho.1.eq_iff (a := i) (b := j)]
  filter_upwards [eventually_exists_eq_lower_mul_borel ε o h_acc, h_acc] with a ha ha_acc ha_mem
  obtain ⟨z, b, hz, hb_mem, hb, (hb'_acc : (1 + z).IsAccretive), -, rfl⟩ := ha ha_mem
  have hb'_mem : 1 + z ∈ blockDiagAlg ε :=
    add_mem (one_mem _) (mem_blockDiagAlg.2 fun i j h_sign ↦ hz i j fun hij ↦ h_sign hij.2)
  have hb' : IsBorelMatrix (-o) (1 + z) := ⟨blockTriangular_one.add fun i j hij ↦
    hz i j fun h_lt ↦ h_lt.1.not_gt (neg_lt_neg_iff.1 hij), hb'_acc.det_ne_zero⟩
  -- Inside the blocks the order `o` is the order of decreasing `l`.
  have hb'_param : IsBorelMatrix l (1 + z) :=
    hb'.of_mem_blockDiagAlg hb'_mem fun i j h_sign hij ↦ neg_lt_neg (h_order h_sign hij)
  have hb_param : IsBorelMatrix (-l) b :=
    hb.of_mem_blockDiagAlg hb_mem fun i j h_sign hij ↦ h_order h_sign.symm (neg_lt_neg_iff.1 hij)
  have h_one : l.flenstedJensen 1 1 = holMinors ε l.lowestKType 1 := by
    simpa [dsCoeff, holMinors] using dsCoeff_one (l := l)
  calc l.flenstedJensen 1 ((1 + z) * b)
      = diagChar l.lowestKType (1 + z) * diagChar l.lowestKType b * l.flenstedJensen 1 1 := by
        simpa only [mul_one] using flenstedJensen_triangular_mul_mul_triangular hl hb'_mem hb'_param
          hb_mem hb_param PosDef.one.isAccretive (by rwa [mul_one])
    _ = holMinors ε l.lowestKType ((1 + z) * b) := by
        rw [h_one, ← holMinors_oppBorel_mul_mul_borel ho h_dom hb' (by simp) hb, mul_one]

/-- Let the order `o` put the signs `1` first. Let the parameter `l` (distinct entries of the parity
of `n - 1`, with some gap `h` between opposite signs) decrease along `o` within each block, and let
its entries at the signs `1` lie below those at the signs `-1`. Then the coefficient `l.dsCoeff`,
the normalised integral of Flensted-Jensen, equals on `U(diag ε)` the model function `holMinors`,
a quotient of products of principal minors, for the highest weight `l.lowestKType` of the lowest
`K`-type. -/
theorem dsCoeff_eq_holMinors_lowestKType (hl : l.HasGap h) (ho : IsPosFirstOrder ε o)
    (h_same : ∀ i j : n, ε i = ε j → o i < o j → l j < l i)
    (h_cross : ∀ i j : n, ε i = 1 → ε j = -1 → l i < l j) (g : USign ε) :
    l.dsCoeff g = holMinors ε l.lowestKType g := by
  -- Both sides are analytic on the group, so it is enough to treat `g = x' * a * x` near `1`.
  refine USign.eq_of_analyticAt_of_eventually_eq l.analyticAt_dsCoeff
    (analyticAt_holMinors l.lowestKType) ?_ g
  have h_dom : IsKDominant ε o l.lowestKType := hl.isKDominant_lowestKType_of_order h_same
  have h_acc : ∀ᶠ z : Matrix n n ℂ in 𝓝 1, z.IsAccretive := PosDef.one.isAccretive.setOf_mem_nhds
  have h_coe : Tendsto (fun g : USign ε ↦ (g : Matrix n n ℂ)) (𝓝 1) (𝓝 1) :=
    Continuous.tendsto' (by fun_prop) 1 1 rfl
  filter_upwards [h_coe.eventually h_acc,
    h_coe.eventually (eventually_exists_eq_corner_mul_mul_corner ε (h_acc.and
      (eventually_flenstedJensen_eq_holMinors_of_mem_blockDiagAlg hl ho h_same)))]
    with g hg_acc hg
  obtain ⟨x', a, x, (hx' : IsInCornerBlock ε (-1) (x' - 1)), ha_mem,
    ⟨(ha_acc : a.IsAccretive), ha_eq⟩, (hx : IsInCornerBlock ε 1 (x - 1)),
    (hg_eq : (g : Matrix n n ℂ) = x' * a * x)⟩ := hg
  -- In the order `o` the factors `x'` and `x` are lower and upper unipotent.
  obtain ⟨h_lower, h_lower_char⟩ : IsBorelMatrix (-o) x' ∧ ∀ w : n → ℤ, diagChar w x' = 1 :=
    hx'.isBorelMatrix_and_diagChar_eq_one (neg_injective.comp ho.1)
      fun i j hi hj ↦ neg_lt_neg (ho.2 j i hj hi)
  obtain ⟨h_upper, h_upper_char⟩ : IsBorelMatrix o x ∧ ∀ w : n → ℤ, diagChar w x = 1 :=
    hx.isBorelMatrix_and_diagChar_eq_one ho.1 ho.2
  calc l.dsCoeff g = l.flenstedJensen 1 g := by
        rw [dsCoeff_eq_flenstedJensen hl (one_mem _) (by simpa using hg_acc), inv_one, one_mul]
    _ = l.flenstedJensen 1 a := by
        rw [hg_eq, flenstedJensen_corner_mul_mul_corner hl h_cross hx' ha_acc.det_ne_zero hx]
    _ = holMinors ε l.lowestKType a := ha_eq ha_mem
    _ = holMinors ε l.lowestKType g := by
        rw [hg_eq, holMinors_oppBorel_mul_mul_borel ho h_dom h_lower ha_acc.det_ne_zero h_upper,
          h_lower_char, h_upper_char, one_mul, one_mul]

end

/-- The holomorphic chamber. Let the order `o` on the `n` indices put the signs `1` first. Let `w`
decrease weakly along `o` within each block of equal signs, and let `w i + γ ≤ w j` for `ε i = 1`,
`ε j = -1`, where `γ > 500 n³ + A + n + 1`. Let `l = 2 w + 2 ρ`, where
`2 ρ a = #{j | o a < o j} - #{j | o j < o a}`; so `l = 2 λ` with `λ a = w a + (n + 1) / 2 - r` for
`r = 1, …, n` the rank of `a` in `o`. Then (a) `l` satisfies `HCParam.HasLargeGap A`, i.e. it is a
parameter for the signs `ε` with gap `500 n³ + A`; (b) for every `g` in the unitary group
`U(diag ε)`, the coefficient `New.HCParam.dsCoeff l g` equals `New.holMinors ε w g`.

Here `dsCoeff` is the normalised integral of Flensted-Jensen and `holMinors` the quotient of
principal minors of weight `w`. -/
theorem dsCoeff_eq_holMinors {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {o : n → ℤ}
    (ho : IsPosFirstOrder ε o) [Nonempty n] (A γ : ℕ) (w : n → ℤ) (hw_dom : IsKDominant ε o w)
    (hw_gap : HasHolGap ε w γ) (hγ : 500 * Fintype.card n ^ 3 + A + Fintype.card n + 1 < γ) :
    let l : HCParam ε := 2 * w + twoRho (-o) ⊤
    l.HasLargeGap A ∧ ∀ g : USign ε, l.dsCoeff g = holMinors ε w g := by
  -- Compute the gap and the lowest `K`-type; then `dsCoeff_eq_holMinors_lowestKType` applies.
  intro l
  have h_inj : o.Injective := ho.1
  have hl_eq (a : n) : l a = 2 * w a + (#{j | o a < o j} - #{j | o j < o a} : ℤ) := by
    simp [l, twoRho]
  -- From here only `hl_eq` is used; `grind` would otherwise unfold `l`.
  clear_value l
  -- Along `o`, `l` decreases inside a block and jumps up by at least `2 (γ - n)` across the blocks.
  have h_same (a b : n) (h_sign : ε a = ε b) (hab : o a < o b) : l b < l a := by
    have h_rho : twoRho o ⊤ a < twoRho o ⊤ b := twoRho_lt_twoRho hab
    simp only [twoRho, Pi.top_apply, Prop.top_eq_true, true_and] at h_rho
    grind [hw_dom a b h_sign hab]
  have h_jump (a b : n) (h_sign : ε a ≠ ε b) (hab : o a < o b) :
      2 * (γ - card n : ℤ) ≤ l b - l a := by
    obtain ⟨ha, hb⟩ : ε a = 1 ∧ ε b = -1 := by
      grind [IsPosFirstOrder, units_eq_one_or (ε a), units_eq_one_or (ε b)]
    -- Each of the two counts in `hl_eq` is less than `card n`.
    grind [hw_gap a b ha hb, card_lt_add_card_gt_add_one h_inj a,
      card_lt_add_card_gt_add_one h_inj b]
  have h_cross (a b : n) (ha : ε a = 1) (hb : ε b = -1) : l a < l b := by
    grind [h_jump a b (by simp [ha, hb]) (ho.2 a b ha hb)]
  have hl_gap : l.HasLargeGap A := by
    have h_distinct : Function.Injective l := fun a b ↦ by
      -- By `h_same` within a block and by `h_jump` across the blocks.
      grind [(o a).lt_or_le (o b), eq_or_ne (ε a) (ε b)]
    have h_parity (a : n) : Even (l a + card n - 1) := by
      -- The two counts in `hl_eq` add up to `card n - 1`.
      grind [card_lt_add_card_gt_add_one h_inj a]
    have h_apart (a b : n) (h_sign : ε a ≠ ε b) : 2 * (gapThreshold n A : ℤ) ≤ |l a - l b| := by
      -- By `h_jump` and `hγ`.
      rw [gapThreshold]
      grind
    exact ⟨h_distinct, h_parity, h_apart⟩
  -- We have `2 * l.lowestKType = l + 2ρ_n - 2ρ_c`, with the sums of the noncompact and the compact
  -- roots positive for `l`. As `l` orders equal signs like `-o` and unequal signs like `o`, these
  -- sums cancel the summand `2ρ` of `l` termwise, which leaves `2 w`.
  have h_cancel (i : n) : (#{j | o i < o j} - #{j | o j < o i} : ℤ) +
      twoRho l (fun a b ↦ ε a ≠ ε b) i - twoRho l (fun a b ↦ ε a = ε b) i = 0 := by
    simp only [twoRho, ← sum_boole, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_eq_zero fun j _ ↦ ?_
    -- Termwise: by `h_same` and `h_jump`, `o i < o j` gives `l j < l i` exactly for equal signs.
    grind
  have h_type : l.lowestKType = w := by
    ext i
    linarith [two_mul_lowestKType hl_gap i, hl_eq i, h_cancel i]
  refine ⟨hl_gap, fun g ↦ ?_⟩
  rw [dsCoeff_eq_holMinors_lowestKType hl_gap ho h_same h_cross, h_type]

end HolomorphicChamber

end New
