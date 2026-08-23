import IntegerPoints.SP3Tail

/-!
# Stationary phase, part 4: the error integral `∫_a^b e(q)(e(r) − 1)`

On a piece `[p, q] ⊆ [a, b]` with `0 ∉ [p, q]`, with `u(x) = (e(r) − 1)/(2πi g''(0) x)` and
`v = e(q)` (so `u v' = e(q)(e(r) − 1)`),
`∫_p^q e(q)(e(r) − 1) = [u e(q)]_p^q − (1/g''(0)) (∫_p^q e(g) r'/x − (1/2πi) ∫_p^q t₂)`,
where `t₂ = e(q)(e(r) − 1)/x²`.  The two integrals are `T₁` (`SP2Parts`) and `T₂`
(`SP3Tail`: the part near `0` by parts, the part with `|x| ≥ δ` by the first-derivative
test applied to `e(g)/x²` and `e(q)/x²`).  Excising `(−ε, ε)` and letting `ε → 0` gives

`‖∫_a^b e(q)(e(r) − 1)‖ ≤ 1/(πλ₂|a|) + 1/(πλ₂b) + (1/(2πλ₂)) (2λ₃/λ₂ + (b − a)B₂ + K₂(δ))`

with `K₂(δ) = 2λ₃/(3λ₂) + (b − a)λ₄/(12λ₂) + πλ₃²δ³/(2λ₂) + 6/(πλ₂δ³)`.
-/

open Real Finset intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace SP

namespace Data

variable (D : Data)

/-- `u(x) = (e(r(x)) − 1) / (2πi g''(0) x)`. -/
noncomputable def u (x : ℝ) : ℂ := (e (D.r x) - 1) / (2 * π * Complex.I * D.g2 0 * x)

theorem norm_u_le_triv {x : ℝ} (hx0 : x ≠ 0) : ‖D.u x‖ ≤ 1 / (π * D.lam₂ * |x|) := by
  unfold u
  have hg20 := D.g2_zero_pos
  have hpi := Real.pi_pos
  have hlam2 := D.hlam₂
  rw [norm_div, norm_mul, norm_mul, PS.norm_two_pi_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hg20, Complex.norm_real, Real.norm_eq_abs]
  have hxa : 0 < |x| := abs_pos.2 hx0
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : ‖e (D.r x) - 1‖ ≤ 2 := by
    calc ‖e (D.r x) - 1‖ ≤ ‖e (D.r x)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [PS.norm_e_one, norm_one]; norm_num
  have h2 := D.g2_pos_at_zero
  calc ‖e (D.r x) - 1‖ * (π * D.lam₂ * |x|) ≤ 2 * (π * D.lam₂ * |x|) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ 1 * (2 * π * D.g2 0 * |x|) := by nlinarith [mul_pos hpi hxa]

theorem norm_u_le_small {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) (hx0 : x ≠ 0) :
    ‖D.u x‖ ≤ D.lam₃ * x ^ 2 / (6 * D.lam₂) := by
  unfold u
  have hg20 := D.g2_zero_pos
  have hpi := Real.pi_pos
  have hlam2 := D.hlam₂
  have hlam3 := D.hlam₃
  rw [norm_div, norm_mul, norm_mul, PS.norm_two_pi_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hg20, Complex.norm_real, Real.norm_eq_abs]
  have hxa : 0 < |x| := abs_pos.2 hx0
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 := norm_e_sub_one_le (D.r x)
  have h2 := D.abs_r_le hx
  have h3 := D.g2_pos_at_zero
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  calc ‖e (D.r x) - 1‖ * (6 * D.lam₂) ≤ 2 * π * (D.lam₃ * |x| ^ 3 / 6) * (6 * D.lam₂) := by
        exact mul_le_mul_of_nonneg_right (h1.trans (by gcongr)) (by positivity)
    _ = D.lam₃ * |x| ^ 2 * (2 * π * D.lam₂ * |x|) := by ring
    _ ≤ D.lam₃ * |x| ^ 2 * (2 * π * D.g2 0 * |x|) := by gcongr
    _ = D.lam₃ * x ^ 2 * (2 * π * D.g2 0 * |x|) := by rw [hx2]

/-- The integrand of the error integral. -/
noncomputable def F (x : ℝ) : ℂ := e (D.q x) * (e (D.r x) - 1)

theorem continuous_F : Continuous D.F := by
  unfold F
  exact (PS.continuous_e_comp D.continuous_q).mul ((PS.continuous_e_comp D.continuous_r).sub continuous_const)

theorem norm_F_le {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) : ‖D.F x‖ ≤ π * D.lam₃ * |x| ^ 3 / 3 := by
  unfold F
  rw [norm_mul, PS.norm_e_one, one_mul]
  have h1 := norm_e_sub_one_le (D.r x)
  have h2 := D.abs_r_le hx
  calc ‖e (D.r x) - 1‖ ≤ 2 * π * |D.r x| := h1
    _ ≤ 2 * π * (D.lam₃ * |x| ^ 3 / 6) := by gcongr
    _ = π * D.lam₃ * |x| ^ 3 / 3 := by ring

/-- **Integration by parts on a piece.** -/
theorem piece_identity {p q : ℝ} (hpq : p ≤ q) (h0 : (0 : ℝ) ∉ Set.Icc p q) :
    ∫ x in p..q, D.F x =
      D.u q * e (D.q q) - D.u p * e (D.q p) -
        (1 / (D.g2 0 : ℂ)) * ((∫ x in p..q, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)) -
          (1 / (2 * π * Complex.I)) * ∫ x in p..q, D.t₂ x) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hg20 := D.g2_zero_pos
  have hIcc : Set.uIcc p q = Set.Icc p q := Set.uIcc_of_le hpq
  have hne : ∀ x ∈ Set.Icc p q, x ≠ 0 := fun x hx h => h0 (h ▸ hx)
  have hI : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hg20' : (D.g2 0 : ℂ) ≠ 0 := by exact_mod_cast hg20.ne'
  -- `u' = (1/g''(0)) (e(r) r'/x − (e(r) − 1)/(2πi x²))`
  set u' : ℝ → ℂ := fun x => (1 / (D.g2 0 : ℂ)) *
    (e (D.r x) * ((D.r1 x / x : ℝ) : ℂ) - (e (D.r x) - 1) / (2 * π * Complex.I * (x : ℂ) ^ 2)) with hu'
  have hud : ∀ x ∈ Set.uIcc p q, HasDerivAt D.u (u' x) x := by
    intro x hx
    rw [hIcc] at hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hne x hx
    unfold u
    have h1 : HasDerivAt (fun y : ℝ => e (D.r y) - 1) (2 * π * Complex.I * D.r1 x * e (D.r x)) x :=
      (PS.hasDerivAt_e_comp (D.hasDerivAt_r x)).sub_const 1
    have h2 : HasDerivAt (fun y : ℝ => (2 * π * Complex.I * D.g2 0 * (y : ℂ)))
        (2 * π * Complex.I * D.g2 0) x := by
      have := ((hasDerivAt_id' x).ofReal_comp).const_mul (2 * π * Complex.I * D.g2 0)
      simpa using this
    have := h1.div h2 (by simp [hI, hg20', hx0])
    refine this.congr_deriv ?_
    rw [hu']
    simp only
    push_cast
    field_simp
  have hvd : ∀ x ∈ Set.uIcc p q,
      HasDerivAt (fun x => e (D.q x))
        (2 * π * Complex.I * ((D.g2 0 * x : ℝ) : ℂ) * e (D.q x)) x :=
    fun x _ => PS.hasDerivAt_e_comp (D.hasDerivAt_q x)
  have hu'i : IntervalIntegrable u' volume p q := by
    apply ContinuousOn.intervalIntegrable
    rw [hIcc, hu']
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.sub
    · apply ContinuousOn.mul (PS.continuous_e_comp D.continuous_r).continuousOn
      apply Complex.continuous_ofReal.comp_continuousOn
      apply ContinuousOn.div D.continuous_r1.continuousOn continuousOn_id
      exact fun x hx => hne x hx
    · apply ContinuousOn.div ((PS.continuous_e_comp D.continuous_r).sub continuous_const).continuousOn
        (continuous_const.mul (Complex.continuous_ofReal.pow 2)).continuousOn
      intro x hx
      have : (x : ℂ) ≠ 0 := by exact_mod_cast hne x hx
      simp [hI, this]
  have hv'i : IntervalIntegrable
      (fun x => 2 * π * Complex.I * ((D.g2 0 * x : ℝ) : ℂ) * e (D.q x)) volume p q :=
    ((continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))).mul
      (PS.continuous_e_comp D.continuous_q)).intervalIntegrable _ _
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hud hvd hu'i hv'i
  have hL : ∫ x in p..q, D.F x =
      ∫ x in p..q, D.u x *
        (2 * π * Complex.I * ((D.g2 0 * x : ℝ) : ℂ) * e (D.q x)) := by
    apply integral_congr
    intro x hx
    rw [hIcc] at hx
    unfold F u
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hne x hx
    push_cast
    field_simp
  rw [hL, h]
  -- rewrite `∫ u' e(q)` as the combination of `T₁` and `T₂`
  have hR : ∫ x in p..q, u' x * e (D.q x) =
      (1 / (D.g2 0 : ℂ)) * ((∫ x in p..q, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)) -
        (1 / (2 * π * Complex.I)) * ∫ x in p..q, D.t₂ x) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub, ← intervalIntegral.integral_const_mul]
    · apply integral_congr
      intro x hx
      rw [hIcc] at hx
      rw [hu']
      simp only
      unfold t₂
      have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hne x hx
      have hg : e (D.g x) = e (D.q x) * e (D.r x) := by rw [D.g_eq_q_add_r, KL.e_add]
      rw [hg]
      field_simp
    · apply ContinuousOn.intervalIntegrable_of_Icc hpq
      apply ContinuousOn.mul (PS.continuous_e_comp D.continuous_g).continuousOn
      apply Complex.continuous_ofReal.comp_continuousOn
      apply ContinuousOn.div D.continuous_r1.continuousOn continuousOn_id
      exact fun x hx => hne x hx
    · apply ContinuousOn.intervalIntegrable_of_Icc hpq
      apply ContinuousOn.mul continuousOn_const
      unfold t₂
      apply ContinuousOn.div
        ((PS.continuous_e_comp D.continuous_q).mul
          ((PS.continuous_e_comp D.continuous_r).sub continuous_const)).continuousOn
        (Complex.continuous_ofReal.pow 2).continuousOn
      intro x hx
      have : (x : ℂ) ≠ 0 := by exact_mod_cast hne x hx
      exact pow_ne_zero 2 this
  rw [hR]

/-! ### The bound on `T₂` over a half-line -/

/-- `K₂(δ)`. -/
noncomputable def K₂ (δ : ℝ) : ℝ :=
  2 * D.lam₃ / (3 * D.lam₂) + (D.b - D.a) * D.lam₄ / (12 * D.lam₂) +
    π * D.lam₃ ^ 2 * δ ^ 3 / (2 * D.lam₂) + 6 / (π * D.lam₂ * δ ^ 3)

theorem t₂_split {p q : ℝ} (hpq : p ≤ q) (h0 : (0 : ℝ) ∉ Set.Icc p q) :
    ∫ x in p..q, D.t₂ x =
      (∫ x in p..q, e (D.g x) / ((x : ℂ) ^ 2)) - ∫ x in p..q, e (D.q x) / ((x : ℂ) ^ 2) := by
  have hne : ∀ x ∈ Set.Icc p q, x ≠ 0 := fun x hx h => h0 (h ▸ hx)
  rw [← intervalIntegral.integral_sub]
  · apply integral_congr
    intro x hx
    rw [Set.uIcc_of_le hpq] at hx
    unfold t₂
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hne x hx
    change e (D.q x) * (e (D.r x) - 1) / (x : ℂ) ^ 2 =
      e (D.g x) / (x : ℂ) ^ 2 - e (D.q x) / (x : ℂ) ^ 2
    rw [D.g_eq_q_add_r, KL.e_add]
    field_simp
  · apply ContinuousOn.intervalIntegrable_of_Icc hpq
    apply ContinuousOn.div (PS.continuous_e_comp D.continuous_g).continuousOn
      (Complex.continuous_ofReal.pow 2).continuousOn
    intro x hx
    exact pow_ne_zero 2 (by exact_mod_cast hne x hx)
  · apply ContinuousOn.intervalIntegrable_of_Icc hpq
    apply ContinuousOn.div (PS.continuous_e_comp D.continuous_q).continuousOn
      (Complex.continuous_ofReal.pow 2).continuousOn
    intro x hx
    exact pow_ne_zero 2 (by exact_mod_cast hne x hx)

theorem T2_q_far {p q m : ℝ} (hpq : p ≤ q) (hm : 0 < m) (h0 : (0 : ℝ) ∉ Set.Icc p q)
    (hmx : ∀ x ∈ Set.Icc p q, m ≤ |x|) :
    ‖∫ x in p..q, e (D.q x) / ((x : ℂ) ^ 2)‖ ≤ 3 / (2 * π * D.lam₂ * m ^ 3) := by
  have hne : ∀ x ∈ Set.Icc p q, x ≠ 0 := fun x hx h => h0 (h ▸ hx)
  exact weighted_first_derivative (φ := D.q) (φ1 := fun x => D.g2 0 * x) (φ2 := fun _ => D.g2 0)
    D.hasDerivAt_q (fun x => by simpa using (hasDerivAt_id' x).const_mul (D.g2 0))
    (by fun_prop) continuous_const
    hpq hm D.hlam₂ hmx
    (fun x hx => by
      have hx0 : x ≠ 0 := hne x hx
      calc
        0 < D.g2 0 * (x * x) := mul_pos D.g2_zero_pos (mul_self_pos.mpr hx0)
        _ = x * (D.g2 0 * x) := by ring)
    (fun x _ => D.g2_zero_pos.le)
    (fun x hx => by
      rw [abs_mul, abs_of_pos D.g2_zero_pos]
      exact mul_le_mul_of_nonneg_right D.g2_pos_at_zero (abs_nonneg _))

theorem T2_g_far {p q m : ℝ} (hpq : p ≤ q) (hm : 0 < m) (h0 : (0 : ℝ) ∉ Set.Icc p q)
    (hsub : Set.Icc p q ⊆ Set.Icc D.a D.b) (hmx : ∀ x ∈ Set.Icc p q, m ≤ |x|) :
    ‖∫ x in p..q, e (D.g x) / ((x : ℂ) ^ 2)‖ ≤ 3 / (2 * π * D.lam₂ * m ^ 3) := by
  have hne : ∀ x ∈ Set.Icc p q, x ≠ 0 := fun x hx h => h0 (h ▸ hx)
  exact weighted_first_derivative (φ := D.g) (φ1 := D.g1) (φ2 := D.g2) D.hasDerivAt_g
    D.hasDerivAt_g1 D.continuous_g1 D.continuous_g2 hpq hm D.hlam₂ hmx
    (fun x hx => by
      have hx0 : x ≠ 0 := hne x hx
      have := D.hlam₂
      rcases lt_or_gt_of_ne hx0 with h | h
      · have hg1neg : D.g1 x < 0 :=
          (D.g1_le_of_nonpos (hsub hx) h.le).trans_lt (mul_neg_of_pos_of_neg D.hlam₂ h)
        exact mul_pos_of_neg_of_neg h hg1neg
      · have hg1pos : 0 < D.g1 x :=
          (mul_pos D.hlam₂ h).trans_le (D.g1_ge_of_nonneg (hsub hx) h.le)
        exact mul_pos h hg1pos)
    (fun x hx => D.hlam₂.le.trans (D.h2 x (hsub hx)))
    (fun x hx => D.abs_g1_ge (hsub hx))

/-- `T₂` over a piece `[p, q] ⊆ [a, b]` with `m ≤ |x|`, `0 ∉ [p, q]`. -/
theorem T2_far {p q m : ℝ} (hpq : p ≤ q) (hm : 0 < m) (h0 : (0 : ℝ) ∉ Set.Icc p q)
    (hsub : Set.Icc p q ⊆ Set.Icc D.a D.b) (hmx : ∀ x ∈ Set.Icc p q, m ≤ |x|) :
    ‖∫ x in p..q, D.t₂ x‖ ≤ 6 / (2 * π * D.lam₂ * m ^ 3) := by
  rw [D.t₂_split hpq h0]
  calc _ ≤ ‖∫ x in p..q, e (D.g x) / ((x : ℂ) ^ 2)‖ + ‖∫ x in p..q, e (D.q x) / ((x : ℂ) ^ 2)‖ :=
        norm_sub_le _ _
    _ ≤ 3 / (2 * π * D.lam₂ * m ^ 3) + 3 / (2 * π * D.lam₂ * m ^ 3) :=
        add_le_add (D.T2_g_far hpq hm h0 hsub hmx) (D.T2_q_far hpq hm h0 hmx)
    _ = _ := by ring

theorem intervalIntegrable_t₂ {p q : ℝ} (hpq : p ≤ q) (h0 : (0 : ℝ) ∉ Set.Icc p q) :
    IntervalIntegrable D.t₂ volume p q := by
  have hne : ∀ x ∈ Set.Icc p q, x ≠ 0 := fun x hx h => h0 (h ▸ hx)
  apply ContinuousOn.intervalIntegrable_of_Icc hpq
  unfold t₂
  apply ContinuousOn.div
    ((PS.continuous_e_comp D.continuous_q).mul
      ((PS.continuous_e_comp D.continuous_r).sub continuous_const)).continuousOn
    (Complex.continuous_ofReal.pow 2).continuousOn
  intro x hx
  exact pow_ne_zero 2 (by exact_mod_cast hne x hx)

/-- The half-line bound, stated for `[p, q]` with `0 < p ≤ q ≤ b` or `a ≤ p ≤ q < 0`:
`‖∫_p^q t₂‖ ≤ λ₃/(3λ₂) + (b − a) λ₄/(24λ₂) + π λ₃² δ³/(4λ₂) + 6/(2π λ₂ δ³)`. -/
theorem T2_half {δ p q : ℝ} (hδ : 0 < δ) (hpq : p ≤ q) (_h0 : (0 : ℝ) ∉ Set.Icc p q)
    (hsub : Set.Icc p q ⊆ Set.Icc D.a D.b) (hpδ : |p| ≤ δ ∨ |q| ≤ δ)
    (hside : 0 < p ∨ q < 0) :
    ‖∫ x in p..q, D.t₂ x‖ ≤ D.lam₃ / (3 * D.lam₂) + (D.b - D.a) * (D.lam₄ / (24 * D.lam₂)) +
      π * D.lam₃ ^ 2 * δ ^ 3 / (4 * D.lam₂) + 6 / (2 * π * D.lam₂ * δ ^ 3) := by
  have hB2 := D.hlam₂
  have hB3 := D.hlam₃
  have hB4 := D.hlam₄
  have hba : 0 ≤ D.b - D.a := by linarith [D.ha, D.hb]
  -- the splitting point `s`: on the right `s = min q δ`, on the left `s = max p (−δ)`
  rcases hside with hp | hq
  · -- right side: `[p, s] ∪ [s, q]`, `s = min q δ`
    set s : ℝ := min q δ with hs
    have hps : p ≤ s := by
      rcases hpδ with h | h
      · rw [abs_of_pos hp] at h; exact le_min hpq h
      · rw [abs_of_pos (by linarith)] at h; exact le_min hpq (hpq.trans h)
    have hsq : s ≤ q := min_le_left _ _
    have hsδ : s ≤ δ := min_le_right _ _
    have hsub1 : Set.Icc p s ⊆ Set.Icc D.a D.b := Set.Icc_subset_Icc (hsub ⟨le_rfl, hpq⟩).1
      (hsq.trans (hsub ⟨hpq, le_rfl⟩).2)
    have hsub2 : Set.Icc s q ⊆ Set.Icc D.a D.b := Set.Icc_subset_Icc
      ((hsub ⟨le_rfl, hpq⟩).1.trans hps) (hsub ⟨hpq, le_rfl⟩).2
    rw [← integral_add_adjacent_intervals (D.intervalIntegrable_t₂ hps (fun h => by linarith [h.1]))
      (D.intervalIntegrable_t₂ hsq (fun h => by linarith [h.1]))]
    have h1 := D.T2_near (p := p) (q := s) (δ := δ) hps (fun h => by linarith [h.1]) hsub1
      (fun x hx => by rw [abs_of_pos (by linarith [hx.1])]; exact hx.2.trans hsδ) hδ.le
    have h2 : ‖∫ x in s..q, D.t₂ x‖ ≤ 6 / (2 * π * D.lam₂ * δ ^ 3) := by
      rcases eq_or_lt_of_le hsq with h | h
      · rw [h, integral_same, norm_zero]
        positivity
      · have hsδ' : s = δ := by
          rw [hs]
          rcases le_or_gt q δ with hqδ | hqδ
          · exfalso
            rw [hs, min_eq_left hqδ] at h
            exact lt_irrefl _ h
          · exact min_eq_right hqδ.le
        rw [hsδ'] at h ⊢
        exact D.T2_far (p := δ) (q := q) h.le hδ (fun h' => by linarith [h'.1])
          (hsδ' ▸ hsub2) (fun x hx => by rw [abs_of_pos (by linarith [hx.1])]; exact hx.1)
    have hsp : s - p ≤ D.b - D.a := by linarith [(hsub ⟨le_rfl, hpq⟩).1, (hsub ⟨hpq, le_rfl⟩).2]
    have hsp' : s - p ≤ δ := by linarith
    have hsp0 : 0 ≤ s - p := by linarith
    calc ‖(∫ x in p..s, D.t₂ x) + ∫ x in s..q, D.t₂ x‖
        ≤ ‖∫ x in p..s, D.t₂ x‖ + ‖∫ x in s..q, D.t₂ x‖ := norm_add_le _ _
      _ ≤ (D.lam₃ / (3 * D.lam₂) +
            (s - p) * (D.lam₄ / (24 * D.lam₂) + π * D.lam₃ ^ 2 * δ ^ 2 / (4 * D.lam₂))) +
          6 / (2 * π * D.lam₂ * δ ^ 3) := add_le_add h1 h2
      _ ≤ (D.lam₃ / (3 * D.lam₂) + ((D.b - D.a) * (D.lam₄ / (24 * D.lam₂)) +
            δ * (π * D.lam₃ ^ 2 * δ ^ 2 / (4 * D.lam₂)))) + 6 / (2 * π * D.lam₂ * δ ^ 3) := by
          gcongr
          rw [mul_add]
          gcongr
      _ = _ := by ring
  · -- left side: `[p, s] ∪ [s, q]`, `s = max p (−δ)`
    set s : ℝ := max p (-δ) with hs
    have hsq : s ≤ q := by
      rcases hpδ with h | h
      · rw [abs_of_neg (by linarith)] at h; exact max_le hpq (by linarith)
      · rw [abs_of_neg hq] at h; exact max_le hpq (by linarith)
    have hps : p ≤ s := le_max_left _ _
    have hsδ : -δ ≤ s := le_max_right _ _
    have hsub1 : Set.Icc s q ⊆ Set.Icc D.a D.b := Set.Icc_subset_Icc
      ((hsub ⟨le_rfl, hpq⟩).1.trans hps) (hsub ⟨hpq, le_rfl⟩).2
    have hsub2 : Set.Icc p s ⊆ Set.Icc D.a D.b := Set.Icc_subset_Icc (hsub ⟨le_rfl, hpq⟩).1
      (hsq.trans (hsub ⟨hpq, le_rfl⟩).2)
    rw [← integral_add_adjacent_intervals (D.intervalIntegrable_t₂ hps (fun h => by linarith [h.2]))
      (D.intervalIntegrable_t₂ hsq (fun h => by linarith [h.2]))]
    have h1 := D.T2_near (p := s) (q := q) (δ := δ) hsq (fun h => by linarith [h.2]) hsub1
      (fun x hx => by rw [abs_of_neg (by linarith [hx.2])]; linarith [hx.1]) hδ.le
    have h2 : ‖∫ x in p..s, D.t₂ x‖ ≤ 6 / (2 * π * D.lam₂ * δ ^ 3) := by
      rcases eq_or_lt_of_le hps with h | h
      · rw [← h, integral_same, norm_zero]
        positivity
      · have hsδ' : s = -δ := by
          rw [hs]
          rcases le_or_gt (-δ) p with hpδ' | hpδ'
          · exfalso
            rw [hs, max_eq_left hpδ'] at h
            exact lt_irrefl _ h
          · exact max_eq_right hpδ'.le
        rw [hsδ'] at h ⊢
        exact D.T2_far (p := p) (q := -δ) h.le hδ (fun h' => by linarith [h'.2])
          (hsδ' ▸ hsub2) (fun x hx => by rw [abs_of_neg (by linarith [hx.2])]; linarith [hx.2])
    have hqs : q - s ≤ D.b - D.a := by linarith [(hsub ⟨le_rfl, hpq⟩).1, (hsub ⟨hpq, le_rfl⟩).2]
    have hqs' : q - s ≤ δ := by linarith
    have hqs0 : 0 ≤ q - s := by linarith
    calc ‖(∫ x in p..s, D.t₂ x) + ∫ x in s..q, D.t₂ x‖
        ≤ ‖∫ x in p..s, D.t₂ x‖ + ‖∫ x in s..q, D.t₂ x‖ := norm_add_le _ _
      _ ≤ 6 / (2 * π * D.lam₂ * δ ^ 3) + (D.lam₃ / (3 * D.lam₂) +
            (q - s) * (D.lam₄ / (24 * D.lam₂) + π * D.lam₃ ^ 2 * δ ^ 2 / (4 * D.lam₂))) :=
          add_le_add h2 h1
      _ ≤ 6 / (2 * π * D.lam₂ * δ ^ 3) + (D.lam₃ / (3 * D.lam₂) + ((D.b - D.a) * (D.lam₄ / (24 * D.lam₂)) +
            δ * (π * D.lam₃ ^ 2 * δ ^ 2 / (4 * D.lam₂)))) := by
          gcongr
          rw [mul_add]
          gcongr
      _ = _ := by ring

/-! ### The total bound -/

/-- `K₂(δ)` is exactly the sum of the two half-line bounds for `T₂`. -/
theorem two_halves_eq_K₂ {δ : ℝ} (hδ : 0 < δ) :
    2 * (D.lam₃ / (3 * D.lam₂) + (D.b - D.a) * (D.lam₄ / (24 * D.lam₂)) +
      π * D.lam₃ ^ 2 * δ ^ 3 / (4 * D.lam₂) + 6 / (2 * π * D.lam₂ * δ ^ 3)) = D.K₂ δ := by
  unfold K₂
  have := D.hlam₂
  have := Real.pi_pos
  field_simp
  ring

/-- A piece `[p, q]` of the error integral, `0 ∉ [p, q]`, `[p, q] ⊆ [a, b]`, lying on one
side of `0` and touching `[−δ, δ]`. -/
theorem piece_bound {δ p q : ℝ} (hδ : 0 < δ) (hpq : p ≤ q) (h0 : (0 : ℝ) ∉ Set.Icc p q)
    (hsub : Set.Icc p q ⊆ Set.Icc D.a D.b) (hpδ : |p| ≤ δ ∨ |q| ≤ δ) (hside : 0 < p ∨ q < 0) :
    ‖∫ x in p..q, D.F x‖ ≤ ‖D.u q‖ + ‖D.u p‖ +
      (1 / D.lam₂) * (1 / (2 * π) * (D.lam₃ / D.lam₂ + (q - p) * D.B₂) +
        1 / (2 * π) * (D.lam₃ / (3 * D.lam₂) + (D.b - D.a) * (D.lam₄ / (24 * D.lam₂)) +
          π * D.lam₃ ^ 2 * δ ^ 3 / (4 * D.lam₂) + 6 / (2 * π * D.lam₂ * δ ^ 3))) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hg20 := D.g2_zero_pos
  rw [D.piece_identity hpq h0]
  have hT1 := D.T1_piece hpq h0 hsub
  have hT2 := D.T2_half hδ hpq h0 hsub hpδ hside
  have hg : ‖(1 / (D.g2 0 : ℂ))‖ ≤ 1 / D.lam₂ := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg20]
    exact one_div_le_one_div_of_le D.hlam₂ D.g2_pos_at_zero
  have hI : ‖(1 / (2 * π * Complex.I) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, PS.norm_two_pi_I]
  have hlam : 0 ≤ 1 / D.lam₂ := one_div_nonneg.mpr D.hlam₂.le
  have hinner : ‖(∫ x in p..q, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)) -
      (1 / (2 * π * Complex.I)) * ∫ x in p..q, D.t₂ x‖ ≤
      ‖∫ x in p..q, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)‖ +
        ‖(1 / (2 * π * Complex.I) : ℂ)‖ * ‖∫ x in p..q, D.t₂ x‖ := by
    calc
      _ ≤ ‖∫ x in p..q, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)‖ +
          ‖(1 / (2 * π * Complex.I)) * ∫ x in p..q, D.t₂ x‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul]
  calc ‖D.u q * e (D.q q) - D.u p * e (D.q p) -
        (1 / (D.g2 0 : ℂ)) * ((∫ x in p..q, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)) -
          (1 / (2 * π * Complex.I)) * ∫ x in p..q, D.t₂ x)‖
      ≤ ‖D.u q * e (D.q q) - D.u p * e (D.q p)‖ +
        ‖(1 / (D.g2 0 : ℂ)) * ((∫ x in p..q, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)) -
          (1 / (2 * π * Complex.I)) * ∫ x in p..q, D.t₂ x)‖ := norm_sub_le _ _
    _ ≤ (‖D.u q * e (D.q q)‖ + ‖D.u p * e (D.q p)‖) +
        ‖(1 / (D.g2 0 : ℂ))‖ * ‖(∫ x in p..q, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)) -
          (1 / (2 * π * Complex.I)) * ∫ x in p..q, D.t₂ x‖ := by
        rw [norm_mul]
        gcongr
        exact norm_sub_le _ _
    _ ≤ (‖D.u q‖ + ‖D.u p‖) +
        (1 / D.lam₂) * (‖∫ x in p..q, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)‖ +
          ‖(1 / (2 * π * Complex.I) : ℂ)‖ * ‖∫ x in p..q, D.t₂ x‖) := by
        apply add_le_add
        · rw [norm_mul, PS.norm_e_one, mul_one, norm_mul, PS.norm_e_one, mul_one]
        · exact mul_le_mul hg hinner (norm_nonneg _) hlam
    _ ≤ (‖D.u q‖ + ‖D.u p‖) +
        (1 / D.lam₂) * (1 / (2 * π) * (D.lam₃ / D.lam₂ + (q - p) * D.B₂) +
          1 / (2 * π) * (D.lam₃ / (3 * D.lam₂) + (D.b - D.a) * (D.lam₄ / (24 * D.lam₂)) +
            π * D.lam₃ ^ 2 * δ ^ 3 / (4 * D.lam₂) + 6 / (2 * π * D.lam₂ * δ ^ 3))) := by
        rw [hI]
        refine add_le_add (le_refl _) ?_
        apply mul_le_mul_of_nonneg_left _ hlam
        exact add_le_add hT1 (mul_le_mul_of_nonneg_left hT2 (by positivity))
    _ = _ := by ring

set_option maxHeartbeats 800000 in
/-- **The error integral** `∫_a^b e(q)(e(r) − 1)`:
`‖∫_a^b F‖ ≤ 1/(πλ₂|a|) + 1/(πλ₂ b) + (1/(2πλ₂)) (2λ₃/λ₂ + (b − a) B₂ + K₂(δ))`. -/
theorem main_bound {δ : ℝ} (hδ : 0 < δ) :
    ‖∫ x in D.a..D.b, D.F x‖ ≤ 1 / (π * D.lam₂ * |D.a|) + 1 / (π * D.lam₂ * D.b) +
      1 / (2 * π * D.lam₂) * (2 * D.lam₃ / D.lam₂ + (D.b - D.a) * D.B₂ + D.K₂ δ) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hl2 := D.hlam₂
  have hl3 := D.hlam₃
  have hl4 := D.hlam₄
  have hB := D.B₂_nonneg
  have hint : ∀ p q : ℝ, IntervalIntegrable D.F volume p q := fun p q =>
    D.continuous_F.intervalIntegrable p q
  set ε₀ : ℝ := min 1 (min (min (-D.a) D.b) δ) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min one_pos (lt_min (lt_min (by linarith [D.ha]) D.hb) hδ)
  -- the constant in front of `ε²`
  apply le_of_forall_small (c := D.lam₃ / (3 * D.lam₂) + 2 * π * D.lam₃ / 3) (by positivity) hε₀0
  intro ε hε hεε₀
  have hε1 : ε ≤ 1 := hεε₀.trans (min_le_left _ _)
  have hεa : ε ≤ -D.a := hεε₀.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hεb : ε ≤ D.b := hεε₀.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hεδ : ε ≤ δ := hεε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  rw [← integral_add_adjacent_intervals (hint D.a (-ε)) (hint (-ε) D.b),
    ← integral_add_adjacent_intervals (hint (-ε) ε) (hint ε D.b)]
  -- the two outer pieces
  have h1 := D.piece_bound (δ := δ) (p := D.a) (q := -ε) hδ (by linarith) (fun h => by linarith [h.2])
    (Set.Icc_subset_Icc le_rfl (by linarith)) (Or.inr (by rw [abs_of_neg (by linarith)]; linarith))
    (Or.inr (by linarith))
  have h3 := D.piece_bound (δ := δ) (p := ε) (q := D.b) hδ hεb (fun h => by linarith [h.1])
    (Set.Icc_subset_Icc (by linarith) le_rfl) (Or.inl (by rw [abs_of_pos hε]; exact hεδ))
    (Or.inl hε)
  -- the middle piece
  have h2 : ‖∫ x in (-ε)..ε, D.F x‖ ≤ 2 * π * D.lam₃ / 3 * ε ^ 2 := by
    have := norm_integral_le_of_norm_le_const (a := -ε) (b := ε) (C := π * D.lam₃ * ε ^ 3 / 3)
      (f := D.F) (fun x hx => by
        rw [Set.uIoc_of_le (by linarith)] at hx
        have hx' : x ∈ Set.Icc D.a D.b := ⟨by linarith [hx.1], by linarith [hx.2]⟩
        refine (D.norm_F_le hx').trans ?_
        have hxε : |x| ≤ ε := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
        have : |x| ^ 3 ≤ ε ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hxε 3
        gcongr)
    rw [abs_of_nonneg (by linarith)] at this
    have hε3 : ε ^ 3 ≤ ε ^ 2 := by
      have : ε ^ 3 = ε ^ 2 * ε := by ring
      rw [this]
      nlinarith [sq_nonneg ε]
    calc _ ≤ (ε - -ε) * (π * D.lam₃ * ε ^ 3 / 3) := by simpa [mul_comm] using this
      _ = 2 * π * D.lam₃ / 3 * ε * ε ^ 3 := by ring
      _ ≤ 2 * π * D.lam₃ / 3 * ε ^ 2 := by
          have : 2 * π * D.lam₃ / 3 * ε * ε ^ 3 = 2 * π * D.lam₃ / 3 * (ε ^ 3 * ε) := by ring
          rw [this]
          gcongr
          calc ε ^ 3 * ε ≤ ε ^ 2 * 1 := by gcongr
            _ = ε ^ 2 := by ring
  -- the boundary terms
  have hua := D.norm_u_le_triv (x := D.a) D.ha.ne
  have hub := D.norm_u_le_triv (x := D.b) D.hb.ne'
  have hume := D.norm_u_le_small (x := -ε) ⟨by linarith, by linarith⟩ (by linarith)
  have hue := D.norm_u_le_small (x := ε) ⟨by linarith, by linarith⟩ hε.ne'
  rw [neg_sq] at hume
  have hK := D.two_halves_eq_K₂ hδ
  -- assemble
  have hsum : ‖(∫ x in D.a..(-ε), D.F x) + ((∫ x in (-ε)..ε, D.F x) + ∫ x in ε..D.b, D.F x)‖ ≤
      ‖∫ x in D.a..(-ε), D.F x‖ + (‖∫ x in (-ε)..ε, D.F x‖ + ‖∫ x in ε..D.b, D.F x‖) := by
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact norm_add_le _ _
  refine hsum.trans ?_
  have e1 : (-ε - D.a) * D.B₂ + (D.b - ε) * D.B₂ ≤ (D.b - D.a) * D.B₂ := by nlinarith
  have hfinal : ‖D.u (-ε)‖ + ‖D.u D.a‖ + ‖D.u D.b‖ + ‖D.u ε‖ ≤
      1 / (π * D.lam₂ * |D.a|) + 1 / (π * D.lam₂ * D.b) + D.lam₃ / (3 * D.lam₂) * ε ^ 2 := by
    have : D.lam₃ * ε ^ 2 / (6 * D.lam₂) + D.lam₃ * ε ^ 2 / (6 * D.lam₂) =
        D.lam₃ / (3 * D.lam₂) * ε ^ 2 := by field_simp; ring
    rw [abs_of_pos D.hb] at hub
    linarith
  calc ‖∫ x in D.a..(-ε), D.F x‖ + (‖∫ x in (-ε)..ε, D.F x‖ + ‖∫ x in ε..D.b, D.F x‖)
      ≤ (‖D.u (-ε)‖ + ‖D.u D.a‖ +
          (1 / D.lam₂) * (1 / (2 * π) * (D.lam₃ / D.lam₂ + (-ε - D.a) * D.B₂) +
            1 / (2 * π) * (D.lam₃ / (3 * D.lam₂) + (D.b - D.a) * (D.lam₄ / (24 * D.lam₂)) +
              π * D.lam₃ ^ 2 * δ ^ 3 / (4 * D.lam₂) + 6 / (2 * π * D.lam₂ * δ ^ 3)))) +
        (2 * π * D.lam₃ / 3 * ε ^ 2 +
          (‖D.u D.b‖ + ‖D.u ε‖ +
            (1 / D.lam₂) * (1 / (2 * π) * (D.lam₃ / D.lam₂ + (D.b - ε) * D.B₂) +
              1 / (2 * π) * (D.lam₃ / (3 * D.lam₂) + (D.b - D.a) * (D.lam₄ / (24 * D.lam₂)) +
                π * D.lam₃ ^ 2 * δ ^ 3 / (4 * D.lam₂) + 6 / (2 * π * D.lam₂ * δ ^ 3))))) :=
        add_le_add h1 (add_le_add h2 h3)
    _ ≤ 1 / (π * D.lam₂ * |D.a|) + 1 / (π * D.lam₂ * D.b) +
        1 / (2 * π * D.lam₂) * (2 * D.lam₃ / D.lam₂ + (D.b - D.a) * D.B₂ + D.K₂ δ) +
        (D.lam₃ / (3 * D.lam₂) + 2 * π * D.lam₃ / 3) * ε ^ 2 := by
        rw [← hK]
        have h4 : (1 / D.lam₂) * (1 / (2 * π) * (D.lam₃ / D.lam₂ + (-ε - D.a) * D.B₂)) +
            (1 / D.lam₂) * (1 / (2 * π) * (D.lam₃ / D.lam₂ + (D.b - ε) * D.B₂)) ≤
            1 / (2 * π * D.lam₂) * (2 * D.lam₃ / D.lam₂ + (D.b - D.a) * D.B₂) := by
          have : (1 / D.lam₂) * (1 / (2 * π) * (D.lam₃ / D.lam₂ + (-ε - D.a) * D.B₂)) +
              (1 / D.lam₂) * (1 / (2 * π) * (D.lam₃ / D.lam₂ + (D.b - ε) * D.B₂)) =
              1 / (2 * π * D.lam₂) * (2 * D.lam₃ / D.lam₂ + ((-ε - D.a) * D.B₂ + (D.b - ε) * D.B₂)) := by
            field_simp
            ring
          rw [this]
          gcongr
        have h5 : (1 / D.lam₂) * (1 / (2 * π) * (D.lam₃ / (3 * D.lam₂) +
              (D.b - D.a) * (D.lam₄ / (24 * D.lam₂)) + π * D.lam₃ ^ 2 * δ ^ 3 / (4 * D.lam₂) +
              6 / (2 * π * D.lam₂ * δ ^ 3))) +
            (1 / D.lam₂) * (1 / (2 * π) * (D.lam₃ / (3 * D.lam₂) +
              (D.b - D.a) * (D.lam₄ / (24 * D.lam₂)) + π * D.lam₃ ^ 2 * δ ^ 3 / (4 * D.lam₂) +
              6 / (2 * π * D.lam₂ * δ ^ 3))) =
            1 / (2 * π * D.lam₂) * (2 * (D.lam₃ / (3 * D.lam₂) +
              (D.b - D.a) * (D.lam₄ / (24 * D.lam₂)) + π * D.lam₃ ^ 2 * δ ^ 3 / (4 * D.lam₂) +
              6 / (2 * π * D.lam₂ * δ ^ 3))) := by
          field_simp
          ring
        nlinarith [hfinal, h4, h5]

end Data

end SP

end LeanProofs.IntegerPoints
