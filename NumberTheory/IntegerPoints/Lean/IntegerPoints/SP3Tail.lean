import IntegerPoints.SP2Parts

/-!
# Stationary phase, part 3: the integral `T₂ = ∫ e(q(x)) (e(r(x)) − 1) / x² dx`

Here `q(x) = g''(0) x²/2`.  Two estimates:

* **Near `0`** (the interval `I = [a, b] ∩ [−δ, δ]`, minus `(−ε, ε)`): with
  `u₂(x) = (e(r(x)) − 1)/x³` and `v(x) = e(q(x))/(2πi g''(0))` (so `v' = x e(q)`),
  `∫ e(q)(e(r) − 1)/x² = [u₂ v] − ∫ u₂' v`.  The derivative
  `u₂' = (2πi Ψ − 3ρ(r) + 2πi x r'(e(r) − 1))/x⁴` with `ρ(y) = e(y) − 1 − 2πiy`
  is bounded by `πλ₄/12 + π²λ₃²x²/2`, and `|u₂| ≤ πλ₃/3`.
* **Away from `0`** (`|x| ≥ m`): for a phase `φ` with `|φ'(x)| ≥ λ₂|x|` and `x φ'(x) > 0`,
  `φ'' > 0`, the weight `1/(x² φ')` is monotone, and integration by parts gives
  `‖∫ e(φ)/x²‖ ≤ 3/(2π λ₂ m³)`.
-/

open Real Finset intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace SP

/-! ### Taylor bounds for `e` -/

theorem hasDerivAt_e (t : ℝ) : HasDerivAt e (2 * π * Complex.I * e t) t := by
  have := PS.hasDerivAt_e_comp (f := fun t : ℝ => t) (hasDerivAt_id' t)
  simpa using this

/-- `‖e(y) − 1‖ ≤ 2π|y|`. -/
theorem norm_e_sub_one_le (y : ℝ) : ‖e y - 1‖ ≤ 2 * π * |y| := by
  have hFTC : ∫ t in (0 : ℝ)..y, 2 * π * Complex.I * e t = e y - e 0 :=
    integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_e t)
      ((continuous_const.mul (PS.continuous_e_comp continuous_id)).intervalIntegrable _ _)
  have he0 : e 0 = 1 := by simp [e]
  rw [he0] at hFTC
  rw [← hFTC]
  have := norm_integral_le_of_norm_le_const (a := 0) (b := y) (C := 2 * π)
    (f := fun t => 2 * π * Complex.I * e t) (fun t _ => by
      rw [norm_mul, PS.norm_e_one, mul_one, PS.norm_two_pi_I])
  rw [sub_zero] at this
  linarith

/-- `‖e(y) − 1 − 2πi y‖ ≤ 2π² y²`. -/
theorem norm_e_sub_one_sub_le (y : ℝ) : ‖e y - 1 - 2 * π * Complex.I * y‖ ≤ 2 * π ^ 2 * y ^ 2 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => e t - 1 - 2 * π * Complex.I * t)
      (2 * π * Complex.I * (e t - 1)) t := by
    intro t
    have h1 := (hasDerivAt_e t).sub_const (1 : ℂ)
    have h2 := ((hasDerivAt_id' t).ofReal_comp).const_mul (2 * π * Complex.I)
    refine (h1.sub h2).congr_deriv ?_
    norm_num
    ring
  have hFTC : ∫ t in (0 : ℝ)..y, 2 * π * Complex.I * (e t - 1) =
      (e y - 1 - 2 * π * Complex.I * y) - (e 0 - 1 - 2 * π * Complex.I * (0 : ℝ)) :=
    integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((continuous_const.mul ((PS.continuous_e_comp continuous_id).sub continuous_const)).intervalIntegrable
        _ _)
  have he0 : e 0 = 1 := by simp [e]
  rw [he0] at hFTC
  simp only [sub_self, Complex.ofReal_zero, mul_zero, sub_zero] at hFTC
  rw [← hFTC]
  -- bound the integrand by `4π²|t|`
  have hb : ∀ t, ‖2 * π * Complex.I * (e t - 1)‖ ≤ 4 * π ^ 2 * |t| := by
    intro t
    rw [norm_mul, PS.norm_two_pi_I]
    have := norm_e_sub_one_le t
    nlinarith [Real.pi_pos]
  rcases le_or_gt 0 y with hy | hy
  · have := norm_integral_le_of_norm_le (μ := volume) hy
      (f := fun t => 2 * π * Complex.I * (e t - 1)) (g := fun t => 4 * π ^ 2 * |t|)
      (Filter.Eventually.of_forall fun t _ => hb t)
      ((by fun_prop : Continuous fun t : ℝ => 4 * π ^ 2 * |t|).intervalIntegrable _ _)
    refine this.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul]
    have h := Data.integral_abs_pow_nonneg hy 1
    simp only [pow_one] at h
    rw [h]
    push_cast
    ring
  · rw [integral_symm, norm_neg]
    have := norm_integral_le_of_norm_le (μ := volume) hy.le
      (f := fun t => 2 * π * Complex.I * (e t - 1)) (g := fun t => 4 * π ^ 2 * |t|)
      (Filter.Eventually.of_forall fun t _ => hb t)
      ((by fun_prop : Continuous fun t : ℝ => 4 * π ^ 2 * |t|).intervalIntegrable _ _)
    refine this.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul]
    have h := Data.integral_abs_pow_nonpos hy.le 1
    simp only [pow_one] at h
    rw [h]
    push_cast
    ring

namespace Data

variable (D : Data)

/-- `q(x) = g''(0) x² / 2`. -/
noncomputable def q (x : ℝ) : ℝ := D.g2 0 * x ^ 2 / 2

theorem hasDerivAt_q (x : ℝ) : HasDerivAt D.q (D.g2 0 * x) x := by
  unfold q
  have := (((hasDerivAt_id' x).pow 2).const_mul (D.g2 0)).div_const 2
  refine this.congr_deriv ?_
  ring

theorem g_eq_q_add_r (x : ℝ) : D.g x = D.q x + D.r x := by
  unfold q r
  ring

theorem continuous_q : Continuous D.q := by
  unfold q
  fun_prop

theorem g2_zero_pos : 0 < D.g2 0 := D.hlam₂.trans_le D.g2_pos_at_zero

/-! ### The piece near `0` -/

/-- `u₂(x) = (e(r(x)) − 1) / x³`. -/
noncomputable def u₂ (x : ℝ) : ℂ := (e (D.r x) - 1) / ((x : ℂ) ^ 3)

/-- `u₂'(x) = (2πi r'(x) x e(r(x)) − 3(e(r(x)) − 1)) / x⁴`. -/
noncomputable def u₂' (x : ℝ) : ℂ :=
  (2 * π * Complex.I * D.r1 x * x * e (D.r x) - 3 * (e (D.r x) - 1)) / ((x : ℂ) ^ 4)

theorem hasDerivAt_u₂ {x : ℝ} (hx : x ≠ 0) : HasDerivAt D.u₂ (D.u₂' x) x := by
  unfold u₂
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have h1 : HasDerivAt (fun y : ℝ => e (D.r y) - 1) (2 * π * Complex.I * D.r1 x * e (D.r x)) x :=
    (PS.hasDerivAt_e_comp (D.hasDerivAt_r x)).sub_const 1
  have h2 : HasDerivAt (fun y : ℝ => ((y : ℂ) ^ 3)) (3 * (x : ℂ) ^ 2) x := by
    have := ((hasDerivAt_id' x).pow 3).ofReal_comp
    simpa using this
  have := h1.div h2 (pow_ne_zero 3 hx')
  refine this.congr_deriv ?_
  unfold u₂'
  field_simp

theorem norm_u₂_le {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) (hx0 : x ≠ 0) :
    ‖D.u₂ x‖ ≤ π * D.lam₃ / 3 := by
  unfold u₂
  have hx' : (0 : ℝ) < |x| ^ 3 := by positivity
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hx']
  have h1 := norm_e_sub_one_le (D.r x)
  have h2 := D.abs_r_le hx
  calc ‖e (D.r x) - 1‖ ≤ 2 * π * |D.r x| := h1
    _ ≤ 2 * π * (D.lam₃ * |x| ^ 3 / 6) := by gcongr
    _ = π * D.lam₃ / 3 * |x| ^ 3 := by ring

theorem norm_u₂'_le {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) (hx0 : x ≠ 0) :
    ‖D.u₂' x‖ ≤ π * D.lam₄ / 12 + π ^ 2 * D.lam₃ ^ 2 * x ^ 2 / 2 := by
  unfold u₂'
  have hx4 : (0 : ℝ) < |x| ^ 4 := by positivity
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hx4]
  -- the numerator: `2πi Ψ − 3ρ(r) + 2πi x r'(e(r) − 1)`
  set ρ : ℂ := e (D.r x) - 1 - 2 * π * Complex.I * D.r x with hρ
  have hnum : 2 * π * Complex.I * D.r1 x * x * e (D.r x) - 3 * (e (D.r x) - 1) =
      2 * π * Complex.I * (D.Ψ x : ℂ) - 3 * ρ +
        2 * π * Complex.I * x * D.r1 x * (e (D.r x) - 1) := by
    rw [hρ]
    unfold Ψ
    push_cast
    ring
  rw [hnum]
  have hΨ := D.abs_Ψ_le hx
  have hρb := norm_e_sub_one_sub_le (D.r x)
  have hr := D.abs_r_le hx
  have hr1 := D.abs_r1_le hx
  have he1 := norm_e_sub_one_le (D.r x)
  have hpi := Real.pi_pos
  have t1 : ‖2 * π * Complex.I * (D.Ψ x : ℂ)‖ ≤ 2 * π * (D.lam₄ * x ^ 4 / 24) := by
    rw [norm_mul, PS.norm_two_pi_I, Complex.norm_real, Real.norm_eq_abs]
    gcongr
  have t2 : ‖3 * ρ‖ ≤ 3 * (2 * π ^ 2 * (D.lam₃ * |x| ^ 3 / 6) ^ 2) := by
    rw [norm_mul, Complex.norm_ofNat]
    gcongr
    have hrsq : D.r x ^ 2 ≤ (D.lam₃ * |x| ^ 3 / 6) ^ 2 := by
      rw [← sq_abs (D.r x)]
      exact pow_le_pow_left₀ (abs_nonneg _) hr 2
    exact hρb.trans (mul_le_mul_of_nonneg_left hrsq (by positivity))
  have t3 : ‖2 * π * Complex.I * x * D.r1 x * (e (D.r x) - 1)‖ ≤
      2 * π * |x| * (D.lam₃ * x ^ 2 / 2) * (2 * π * (D.lam₃ * |x| ^ 3 / 6)) := by
    rw [norm_mul, norm_mul, norm_mul, PS.norm_two_pi_I, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs]
    have hlam3 := D.hlam₃
    have hcoef : 0 ≤ 2 * π * |x| := by positivity
    have hr1b : 0 ≤ D.lam₃ * x ^ 2 / 2 := by positivity
    have heb : ‖e (D.r x) - 1‖ ≤ 2 * π * (D.lam₃ * |x| ^ 3 / 6) :=
      he1.trans (by gcongr)
    calc
      2 * π * |x| * |D.r1 x| * ‖e (D.r x) - 1‖ ≤
          2 * π * |x| * (D.lam₃ * x ^ 2 / 2) * ‖e (D.r x) - 1‖ := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr1 hcoef) (norm_nonneg _)
      _ ≤ 2 * π * |x| * (D.lam₃ * x ^ 2 / 2) *
          (2 * π * (D.lam₃ * |x| ^ 3 / 6)) := by
            exact mul_le_mul_of_nonneg_left heb (mul_nonneg hcoef hr1b)
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hx4' : x ^ 4 = |x| ^ 4 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, sq_abs]
  calc ‖2 * π * Complex.I * (D.Ψ x : ℂ) - 3 * ρ +
        2 * π * Complex.I * x * D.r1 x * (e (D.r x) - 1)‖
      ≤ ‖2 * π * Complex.I * (D.Ψ x : ℂ) - 3 * ρ‖ +
        ‖2 * π * Complex.I * x * D.r1 x * (e (D.r x) - 1)‖ := norm_add_le _ _
    _ ≤ (‖2 * π * Complex.I * (D.Ψ x : ℂ)‖ + ‖3 * ρ‖) +
        ‖2 * π * Complex.I * x * D.r1 x * (e (D.r x) - 1)‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ 2 * π * (D.lam₄ * x ^ 4 / 24) + 3 * (2 * π ^ 2 * (D.lam₃ * |x| ^ 3 / 6) ^ 2) +
        2 * π * |x| * (D.lam₃ * x ^ 2 / 2) * (2 * π * (D.lam₃ * |x| ^ 3 / 6)) :=
        add_le_add (add_le_add t1 t2) t3
    _ = (π * D.lam₄ / 12 + π ^ 2 * D.lam₃ ^ 2 * x ^ 2 / 2) * |x| ^ 4 := by
        rw [hx2, hx4']
        ring

theorem continuousOn_u₂' {p q : ℝ} (h0 : (0 : ℝ) ∉ Set.Icc p q) :
    ContinuousOn D.u₂' (Set.Icc p q) := by
  unfold u₂'
  apply ContinuousOn.div
  · exact ((((continuous_const.mul (Complex.continuous_ofReal.comp D.continuous_r1)).mul
      Complex.continuous_ofReal).mul (PS.continuous_e_comp D.continuous_r)).sub
      (continuous_const.mul ((PS.continuous_e_comp D.continuous_r).sub continuous_const))).continuousOn
  · exact (Complex.continuous_ofReal.pow 4).continuousOn
  · intro x hx
    have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
    exact pow_ne_zero 4 (by exact_mod_cast hx0)

/-- The `T₂` integrand. -/
noncomputable def t₂ (x : ℝ) : ℂ := e (D.q x) * (e (D.r x) - 1) / ((x : ℂ) ^ 2)

/-- **The piece of `T₂` near `0`**: for `[p, q] ⊆ [a, b]` with `0 ∉ [p, q]` and `|x| ≤ δ` on it. -/
theorem T2_near {p q δ : ℝ} (hpq : p ≤ q) (h0 : (0 : ℝ) ∉ Set.Icc p q)
    (hsub : Set.Icc p q ⊆ Set.Icc D.a D.b) (hδ : ∀ x ∈ Set.Icc p q, |x| ≤ δ) (_hδ0 : 0 ≤ δ) :
    ‖∫ x in p..q, D.t₂ x‖ ≤
      D.lam₃ / (3 * D.lam₂) + (q - p) * (D.lam₄ / (24 * D.lam₂) + π * D.lam₃ ^ 2 * δ ^ 2 / (4 * D.lam₂)) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hg20 := D.g2_zero_pos
  have hIcc : Set.uIcc p q = Set.Icc p q := Set.uIcc_of_le hpq
  have hne : ∀ x ∈ Set.Icc p q, x ≠ 0 := fun x hx h => h0 (h ▸ hx)
  have hI : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hg20' : (D.g2 0 : ℂ) ≠ 0 := by exact_mod_cast hg20.ne'
  -- `v(x) = e(q(x)) / (2πi g''(0))`, `v' = x e(q(x))`
  have hv : ∀ x ∈ Set.uIcc p q, HasDerivAt (fun x => e (D.q x) / (2 * π * Complex.I * D.g2 0))
      ((x : ℂ) * e (D.q x)) x := by
    intro x _
    have := (PS.hasDerivAt_e_comp (D.hasDerivAt_q x)).div_const (2 * π * Complex.I * D.g2 0)
    refine this.congr_deriv ?_
    field_simp
    push_cast
    ring
  have hu : ∀ x ∈ Set.uIcc p q, HasDerivAt D.u₂ (D.u₂' x) x := fun x hx => by
    rw [hIcc] at hx
    exact D.hasDerivAt_u₂ (hne x hx)
  have hu'i : IntervalIntegrable D.u₂' volume p q := by
    apply ContinuousOn.intervalIntegrable
    rw [hIcc]
    exact D.continuousOn_u₂' h0
  have hv'i : IntervalIntegrable (fun x => (x : ℂ) * e (D.q x)) volume p q :=
    (Complex.continuous_ofReal.mul (PS.continuous_e_comp D.continuous_q)).intervalIntegrable _ _
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'i hv'i
  have hL : ∫ x in p..q, D.t₂ x = ∫ x in p..q, D.u₂ x * ((x : ℂ) * e (D.q x)) := by
    apply integral_congr
    intro x hx
    rw [hIcc] at hx
    unfold t₂ u₂
    have : (x : ℂ) ≠ 0 := by exact_mod_cast hne x hx
    field_simp
  rw [hL, h]
  have hvb : ∀ x, ‖e (D.q x) / (2 * π * Complex.I * D.g2 0)‖ ≤ 1 / (2 * π * D.lam₂) := by
    intro x
    rw [norm_div, PS.norm_e_one, norm_mul, PS.norm_two_pi_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hg20]
    apply one_div_le_one_div_of_le (by
      have := D.hlam₂
      positivity)
    have := D.g2_pos_at_zero
    nlinarith
  have hub : ∀ x ∈ Set.Icc p q, ‖D.u₂ x‖ ≤ π * D.lam₃ / 3 :=
    fun x hx => D.norm_u₂_le (hsub hx) (hne x hx)
  have hint : ‖∫ x in p..q, D.u₂' x * (e (D.q x) / (2 * π * Complex.I * D.g2 0))‖ ≤
      (q - p) * ((π * D.lam₄ / 12 + π ^ 2 * D.lam₃ ^ 2 * δ ^ 2 / 2) * (1 / (2 * π * D.lam₂))) := by
    have := norm_integral_le_of_norm_le_const (a := p) (b := q)
      (C := (π * D.lam₄ / 12 + π ^ 2 * D.lam₃ ^ 2 * δ ^ 2 / 2) * (1 / (2 * π * D.lam₂)))
      (f := fun x => D.u₂' x * (e (D.q x) / (2 * π * Complex.I * D.g2 0))) (fun x hx => by
        rw [Set.uIoc_of_le hpq] at hx
        have hx' : x ∈ Set.Icc p q := ⟨hx.1.le, hx.2⟩
        rw [norm_mul]
        apply mul_le_mul _ (hvb x) (norm_nonneg _) (by have := D.hlam₃; have := D.hlam₄; positivity)
        refine (D.norm_u₂'_le (hsub hx') (hne x hx')).trans ?_
        have hxδ := hδ x hx'
        have : x ^ 2 ≤ δ ^ 2 := by rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg _) hxδ 2
        gcongr)
    rw [abs_of_nonneg (by linarith)] at this
    simpa [mul_comm] using this
  have hB : ‖D.u₂ q * (e (D.q q) / (2 * π * Complex.I * D.g2 0)) -
      D.u₂ p * (e (D.q p) / (2 * π * Complex.I * D.g2 0))‖ ≤
      2 * (π * D.lam₃ / 3 * (1 / (2 * π * D.lam₂))) := by
    have hlam3 := D.hlam₃
    have hconst : 0 ≤ π * D.lam₃ / 3 := by positivity
    calc _ ≤ ‖D.u₂ q * (e (D.q q) / (2 * π * Complex.I * D.g2 0))‖ +
          ‖D.u₂ p * (e (D.q p) / (2 * π * Complex.I * D.g2 0))‖ := norm_sub_le _ _
      _ ≤ π * D.lam₃ / 3 * (1 / (2 * π * D.lam₂)) + π * D.lam₃ / 3 * (1 / (2 * π * D.lam₂)) := by
          gcongr
          · rw [norm_mul]
            exact mul_le_mul (hub q ⟨hpq, le_rfl⟩) (hvb q) (norm_nonneg _) hconst
          · rw [norm_mul]
            exact mul_le_mul (hub p ⟨le_rfl, hpq⟩) (hvb p) (norm_nonneg _) hconst
      _ = _ := by ring
  calc ‖D.u₂ q * (e (D.q q) / (2 * π * Complex.I * D.g2 0)) -
        D.u₂ p * (e (D.q p) / (2 * π * Complex.I * D.g2 0)) -
        ∫ x in p..q, D.u₂' x * (e (D.q x) / (2 * π * Complex.I * D.g2 0))‖
      ≤ ‖D.u₂ q * (e (D.q q) / (2 * π * Complex.I * D.g2 0)) -
        D.u₂ p * (e (D.q p) / (2 * π * Complex.I * D.g2 0))‖ +
        ‖∫ x in p..q, D.u₂' x * (e (D.q x) / (2 * π * Complex.I * D.g2 0))‖ := norm_sub_le _ _
    _ ≤ 2 * (π * D.lam₃ / 3 * (1 / (2 * π * D.lam₂))) +
        (q - p) * ((π * D.lam₄ / 12 + π ^ 2 * D.lam₃ ^ 2 * δ ^ 2 / 2) * (1 / (2 * π * D.lam₂))) :=
        add_le_add hB hint
    _ = D.lam₃ / (3 * D.lam₂) +
        (q - p) * (D.lam₄ / (24 * D.lam₂) + π * D.lam₃ ^ 2 * δ ^ 2 / (4 * D.lam₂)) := by
        have := D.hlam₂
        field_simp
        ring

end Data

/-! ### The piece away from `0`: the first-derivative test with weight `1/x²` -/

/-- For a phase `φ` with `φ' = φ1`, `φ1' = φ2` on `[p, q]`, `0 ∉ [p, q]`, `m ≤ |x|`,
`λ|x| ≤ |φ1(x)|`, and the sign conditions `0 < x φ1(x)`, `0 ≤ φ2(x)`:
`‖∫_p^q e(φ)/x²‖ ≤ 3/(2π λ m³)`. -/
theorem weighted_first_derivative {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (φ1 x) x)
    (hφ1 : ∀ x, HasDerivAt φ1 (φ2 x) x) (hφ1c : Continuous φ1) (hφ2c : Continuous φ2)
    {p q m lam : ℝ} (hpq : p ≤ q) (hm : 0 < m) (hlam : 0 < lam)
    (hmx : ∀ x ∈ Set.Icc p q, m ≤ |x|) (hsign : ∀ x ∈ Set.Icc p q, 0 < x * φ1 x)
    (hφ2 : ∀ x ∈ Set.Icc p q, 0 ≤ φ2 x) (hlow : ∀ x ∈ Set.Icc p q, lam * |x| ≤ |φ1 x|) :
    ‖∫ x in p..q, e (φ x) / ((x : ℂ) ^ 2)‖ ≤ 3 / (2 * π * lam * m ^ 3) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hIcc : Set.uIcc p q = Set.Icc p q := Set.uIcc_of_le hpq
  have hne : ∀ x ∈ Set.Icc p q, x ≠ 0 ∧ φ1 x ≠ 0 := by
    intro x hx
    have := hsign x hx
    constructor
    · intro h; rw [h, zero_mul] at this; exact lt_irrefl _ this
    · intro h; rw [h, mul_zero] at this; exact lt_irrefl _ this
  -- `u(x) = 1/(x² φ1(x))`, `u' = −(2x φ1 + x² φ2)/(x² φ1)²`
  set u : ℝ → ℝ := fun x => 1 / (x ^ 2 * φ1 x) with hu
  set u' : ℝ → ℝ := fun x => -((2 * x * φ1 x + x ^ 2 * φ2 x) / (x ^ 2 * φ1 x) ^ 2) with hu'
  have hud : ∀ x ∈ Set.Icc p q, HasDerivAt u (u' x) x := by
    intro x hx
    have hd : HasDerivAt (fun y => y ^ 2 * φ1 y) (2 * x * φ1 x + x ^ 2 * φ2 x) x := by
      have := ((hasDerivAt_id' x).pow 2).mul (hφ1 x)
      refine this.congr_deriv ?_
      simp only [Pi.pow_apply]
      ring
    have hden : x ^ 2 * φ1 x ≠ 0 := mul_ne_zero (pow_ne_zero 2 (hne x hx).1) (hne x hx).2
    have := (hasDerivAt_const x (1 : ℝ)).div hd hden
    refine this.congr_deriv ?_
    rw [hu']
    ring
  have hu'nonpos : ∀ x ∈ Set.Icc p q, u' x ≤ 0 := by
    intro x hx
    rw [hu']
    simp only
    apply neg_nonpos.2
    apply div_nonneg _ (by positivity)
    have h1 := hsign x hx
    have h2 := hφ2 x hx
    nlinarith [sq_nonneg x]
  have hu'c : ContinuousOn u' (Set.Icc p q) := by
    rw [hu']
    apply ContinuousOn.neg
    apply ContinuousOn.div
    · exact ((continuous_const.mul continuous_id |>.mul hφ1c).add
        ((continuous_pow 2).mul hφ2c)).continuousOn
    · exact (((continuous_pow 2).mul hφ1c).pow 2).continuousOn
    · intro x hx
      exact pow_ne_zero 2 (mul_ne_zero (pow_ne_zero 2 (hne x hx).1) (hne x hx).2)
  have hub : ∀ x ∈ Set.Icc p q, |u x| ≤ 1 / (lam * m ^ 3) := by
    intro x hx
    rw [hu]
    simp only
    rw [abs_div, abs_one, abs_mul, abs_pow]
    apply one_div_le_one_div_of_le (by positivity)
    have h1 := hlow x hx
    have h2 := hmx x hx
    calc lam * m ^ 3 = m ^ 2 * (lam * m) := by ring
      _ ≤ |x| ^ 2 * (lam * |x|) := by gcongr
      _ ≤ |x| ^ 2 * |φ1 x| := by gcongr
  -- integration by parts: `∫ e(φ)/x² = (1/2πi)(∫ u · (e∘φ)')`
  have hv : ∀ x ∈ Set.uIcc p q, HasDerivAt (fun x => e (φ x)) (2 * π * Complex.I * φ1 x * e (φ x)) x :=
    fun x _ => PS.hasDerivAt_e_comp (hφ x)
  have hud' : ∀ x ∈ Set.uIcc p q, HasDerivAt (fun x => ((u x : ℝ) : ℂ)) ((u' x : ℝ) : ℂ) x :=
    fun x hx => by rw [hIcc] at hx; exact (hud x hx).ofReal_comp
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hud' hv
    (by
      apply ContinuousOn.intervalIntegrable
      rw [hIcc]
      exact Complex.continuous_ofReal.comp_continuousOn hu'c)
    (((continuous_const.mul (Complex.continuous_ofReal.comp hφ1c)).mul
      (PS.continuous_e_comp (continuous_iff_continuousAt.2 fun x => (hφ x).continuousAt))).intervalIntegrable
      _ _)
  have hI : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hL : ∫ x in p..q, e (φ x) / ((x : ℂ) ^ 2) =
      (1 / (2 * π * Complex.I)) * ∫ x in p..q, ((u x : ℝ) : ℂ) * (2 * π * Complex.I * φ1 x * e (φ x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro x hx
    rw [hIcc] at hx
    simp only
    rw [hu]
    simp only
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (hne x hx).1
    have hφ0 : (φ1 x : ℂ) ≠ 0 := by exact_mod_cast (hne x hx).2
    push_cast
    field_simp
  rw [hL, h, norm_mul, norm_div, norm_one, PS.norm_two_pi_I]
  -- `∫|u'| = u(p) − u(q)`
  have hFTC : ∫ x in p..q, u' x = u q - u p :=
    integral_eq_sub_of_hasDerivAt (fun x hx => hud x (hIcc ▸ hx)) (hu'c.intervalIntegrable_of_Icc hpq)
  have hint : ‖∫ x in p..q, ((u' x : ℝ) : ℂ) * e (φ x)‖ ≤ 1 / (lam * m ^ 3) := by
    calc ‖∫ x in p..q, ((u' x : ℝ) : ℂ) * e (φ x)‖
        ≤ ∫ x in p..q, ‖((u' x : ℝ) : ℂ) * e (φ x)‖ := norm_integral_le_integral_norm hpq
      _ = ∫ x in p..q, -u' x := by
          apply integral_congr
          intro x hx
          rw [hIcc] at hx
          simp only
          rw [norm_mul, PS.norm_e_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonpos (hu'nonpos x hx)]
      _ = u p - u q := by rw [intervalIntegral.integral_neg, hFTC]; ring
      _ ≤ 1 / (lam * m ^ 3) := by
          rcases le_or_gt 0 p with hp | hp
          · have hp0 : 0 < p := lt_of_le_of_ne hp (hne p ⟨le_rfl, hpq⟩).1.symm
            have hq0 : 0 < q := lt_of_lt_of_le hp0 hpq
            have hφq : 0 < φ1 q := pos_of_mul_pos_right (hsign q ⟨hpq, le_rfl⟩) hq0.le
            have huq : 0 ≤ u q := by
              rw [hu]
              exact one_div_nonneg.mpr (mul_nonneg (sq_nonneg q) hφq.le)
            have hup : u p ≤ |u p| := le_abs_self _
            linarith [hub p ⟨le_rfl, hpq⟩]
          · have hφp : φ1 p < 0 := neg_of_mul_pos_right (hsign p ⟨le_rfl, hpq⟩) hp.le
            have hup : u p ≤ 0 := by
              rw [hu]
              exact one_div_nonpos.mpr (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg p) hφp.le)
            have huq : -u q ≤ |u q| := neg_le_abs _
            linarith [hub q ⟨hpq, le_rfl⟩]
  have hB : ‖((u q : ℝ) : ℂ) * e (φ q) - ((u p : ℝ) : ℂ) * e (φ p) -
      ∫ x in p..q, ((u' x : ℝ) : ℂ) * e (φ x)‖ ≤ 3 / (lam * m ^ 3) := by
    calc _ ≤ ‖((u q : ℝ) : ℂ) * e (φ q) - ((u p : ℝ) : ℂ) * e (φ p)‖ +
          ‖∫ x in p..q, ((u' x : ℝ) : ℂ) * e (φ x)‖ := norm_sub_le _ _
      _ ≤ (‖((u q : ℝ) : ℂ) * e (φ q)‖ + ‖((u p : ℝ) : ℂ) * e (φ p)‖) + 1 / (lam * m ^ 3) := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ (1 / (lam * m ^ 3) + 1 / (lam * m ^ 3)) + 1 / (lam * m ^ 3) := by
          gcongr
          · rw [norm_mul, PS.norm_e_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
            exact hub q ⟨hpq, le_rfl⟩
          · rw [norm_mul, PS.norm_e_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
            exact hub p ⟨le_rfl, hpq⟩
      _ = 3 / (lam * m ^ 3) := by ring
  calc 1 / (2 * π) * ‖((u q : ℝ) : ℂ) * e (φ q) - ((u p : ℝ) : ℂ) * e (φ p) -
        ∫ x in p..q, ((u' x : ℝ) : ℂ) * e (φ x)‖
      ≤ 1 / (2 * π) * (3 / (lam * m ^ 3)) := by gcongr
    _ = 3 / (2 * π * lam * m ^ 3) := by
        field_simp

end SP

end LeanProofs.IntegerPoints
