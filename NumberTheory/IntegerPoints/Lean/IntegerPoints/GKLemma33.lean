import IntegerPoints.GKLemma32
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Graham–Kolesnik, Lemma 3.3 (the Fresnel integral)

`∫_{-X}^{X} e(A x²) dx = e(1/8)/√(2A) + O(1/(AX))` for `A, X > 0`.

Proof (by Gaussian regularisation instead of the book's contour integral).
For `ε > 0` put `b = ε − 2πiA`, so `exp(−b x²) = e^{−εx²} e(Ax²)` and
`∫_ℝ exp(−b x²) = (π/b)^{1/2}` (Mathlib's complex Gaussian integral).  Integration
by parts on `[X, R]` with `u = 1/(−2bx)`, `v = exp(−bx²)` gives
`|∫_X^R exp(−bx²)| ≤ 1/(|b|X) + 1/(2|b|R)`, hence `|∫_X^∞| ≤ 1/(|b|X) ≤ 1/(2πAX)`,
and the same for the left tail by evenness; so
`|∫_{-X}^{X} exp(−bx²) − (π/b)^{1/2}| ≤ 1/(πAX)`.  Finally
`|∫_{-X}^{X} (exp(−bx²) − e(Ax²))| ≤ 2εX³ → 0` and `(π/b)^{1/2} → (i/(2A))^{1/2}
= e(1/8)/√(2A)` as `ε → 0⁺`.
-/

open Real Finset intervalIntegral MeasureTheory Filter Topology

namespace LeanProofs.IntegerPoints

namespace GK33

/-- The regularised Gaussian parameter `b(ε) = ε − 2πiA`. -/
noncomputable def bε (A ε : ℝ) : ℂ := (ε : ℂ) - 2 * Real.pi * Complex.I * A

theorem bε_re (A ε : ℝ) : (bε A ε).re = ε := by simp [bε]

theorem bε_im (A ε : ℝ) : (bε A ε).im = -(2 * Real.pi * A) := by simp [bε]

theorem norm_bε_ge {A ε : ℝ} (hA : 0 < A) : 2 * Real.pi * A ≤ ‖bε A ε‖ := by
  have := Complex.abs_im_le_norm (bε A ε)
  rw [bε_im, abs_neg, abs_of_pos (by positivity)] at this
  exact this

theorem bε_ne_zero {A ε : ℝ} (hA : 0 < A) : bε A ε ≠ 0 := by
  intro h
  have := norm_bε_ge (ε := ε) hA
  rw [h, norm_zero] at this
  nlinarith [Real.pi_pos]

/-- `exp(−b x²) = e^{−εx²} · e(Ax²)`. -/
theorem cexp_bε (A ε x : ℝ) :
    Complex.exp (-bε A ε * (x : ℂ) ^ 2) = (Real.exp (-ε * x ^ 2) : ℂ) * e (A * x ^ 2) := by
  unfold e bε
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_cexp_bε (A ε x : ℝ) :
    ‖Complex.exp (-bε A ε * (x : ℂ) ^ 2)‖ = Real.exp (-ε * x ^ 2) := by
  rw [cexp_bε, norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- The tail bound on a finite interval `[X, R]`, by integration by parts. -/
theorem tail_bound {b : ℂ} (hb : b ≠ 0) {X R : ℝ} (hX : 0 < X) (hXR : X ≤ R)
    (hre : 0 ≤ b.re) :
    ‖∫ x in X..R, Complex.exp (-b * (x : ℂ) ^ 2)‖ ≤ 1 / (‖b‖ * X) + 1 / (2 * ‖b‖ * R) := by
  have hb0 : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hR : 0 < R := by linarith
  -- `u = 1/(−2bx)`, `v = exp(−bx²)`
  set u : ℝ → ℂ := fun x => 1 / (-2 * b * x) with hu
  set u' : ℝ → ℂ := fun x => 1 / (2 * b * (x : ℂ) ^ 2) with hu'
  set v : ℝ → ℂ := fun x => Complex.exp (-b * (x : ℂ) ^ 2) with hv
  set v' : ℝ → ℂ := fun x => -2 * b * x * Complex.exp (-b * (x : ℂ) ^ 2) with hv'
  have hIcc : Set.uIcc X R = Set.Icc X R := Set.uIcc_of_le hXR
  have hxne : ∀ x ∈ Set.Icc X R, (x : ℂ) ≠ 0 := by
    intro x hx
    exact_mod_cast (by linarith [hx.1] : x ≠ 0)
  have hud : ∀ x ∈ Set.uIcc X R, HasDerivAt u (u' x) x := by
    intro x hx
    rw [hIcc] at hx
    have hx0 : (x : ℂ) ≠ 0 := hxne x hx
    have h1 : HasDerivAt (fun y : ℝ => (-2 * b * (y : ℂ))) (-2 * b) x := by
      have := (hasDerivAt_id x).ofReal_comp.const_mul (-2 * b)
      simpa using this
    have h2 := h1.inv (by
      simp only [ne_eq, mul_eq_zero, neg_eq_zero, OfNat.ofNat_ne_zero, false_or, not_or]
      exact ⟨hb, hx0⟩)
    have h3 : HasDerivAt u (-(-2 * b) / (-2 * b * (x : ℂ)) ^ 2) x := by
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      simp only [hu, one_div, Pi.inv_apply]
    refine h3.congr_deriv ?_
    rw [hu']
    first | (field_simp; done) | (field_simp; ring)
  have hvd : ∀ x ∈ Set.uIcc X R, HasDerivAt v (v' x) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => (-b * (y : ℂ) ^ 2)) (-b * (2 * (x : ℂ))) x := by
      have := ((hasDerivAt_id x).ofReal_comp.pow 2).const_mul (-b)
      simpa using this
    refine (h1.cexp).congr_deriv ?_
    rw [hv']
    ring
  have hu'c : ContinuousOn u' (Set.uIcc X R) := by
    rw [hIcc, hu']
    apply ContinuousOn.div continuousOn_const
    · exact (continuous_const.mul (Complex.continuous_ofReal.pow 2)).continuousOn
    · intro x hx
      exact mul_ne_zero (mul_ne_zero two_ne_zero hb) (pow_ne_zero 2 (hxne x hx))
  have hv'c : Continuous v' := by
    rw [hv']
    exact (continuous_const.mul Complex.continuous_ofReal).mul
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.pow 2)))
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hud hvd hu'c.intervalIntegrable
    (hv'c.intervalIntegrable _ _)
  have hint : ∫ x in X..R, Complex.exp (-b * (x : ℂ) ^ 2) = ∫ x in X..R, u x * v' x := by
    apply integral_congr
    intro x hx
    rw [hIcc] at hx
    rw [hu, hv']
    simp only
    have hx0 : (x : ℂ) ≠ 0 := hxne x hx
    field_simp
  rw [hint, hparts]
  -- norms of the pieces
  have hvb : ∀ x : ℝ, ‖v x‖ ≤ 1 := by
    intro x
    rw [hv]
    simp only
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.2
    have : (-b * (x : ℂ) ^ 2).re = -(b.re * x ^ 2) := by
      simp [Complex.mul_re, ← Complex.ofReal_pow]
    rw [this]
    nlinarith [sq_nonneg x]
  have hub : ∀ x : ℝ, 0 < x → ‖u x‖ = 1 / (2 * ‖b‖ * x) := by
    intro x hx
    rw [hu]
    simp only
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx]
    simp
  have hu'b : ∀ x : ℝ, 0 < x → ‖u' x‖ = 1 / (2 * ‖b‖ * x ^ 2) := by
    intro x hx
    rw [hu']
    simp only
    rw [norm_div, norm_one, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx]
    simp
  have hbd : ‖u R * v R - u X * v X‖ ≤ 1 / (2 * ‖b‖ * R) + 1 / (2 * ‖b‖ * X) := by
    calc ‖u R * v R - u X * v X‖ ≤ ‖u R‖ * ‖v R‖ + ‖u X‖ * ‖v X‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ 1 / (2 * ‖b‖ * R) * 1 + 1 / (2 * ‖b‖ * X) * 1 := by
          rw [hub R hR, hub X hX]
          gcongr
          · exact hvb R
          · exact hvb X
      _ = 1 / (2 * ‖b‖ * R) + 1 / (2 * ‖b‖ * X) := by ring
  have hI : ‖∫ x in X..R, u' x * v x‖ ≤ 1 / (2 * ‖b‖ * X) := by
    calc ‖∫ x in X..R, u' x * v x‖ ≤ ∫ x in X..R, ‖u' x * v x‖ :=
          norm_integral_le_integral_norm hXR
      _ ≤ ∫ x in X..R, 1 / (2 * ‖b‖ * x ^ 2) := by
          apply integral_mono_on hXR
          · have hvc : ContinuousOn v (Set.uIcc X R) := by
              rw [hv]
              exact (Complex.continuous_exp.comp (continuous_const.mul
                (Complex.continuous_ofReal.pow 2))).continuousOn
            exact (hu'c.mul hvc).norm.intervalIntegrable
          · apply ContinuousOn.intervalIntegrable
            rw [hIcc]
            apply ContinuousOn.div continuousOn_const
            · exact (continuous_const.mul (continuous_id.pow 2)).continuousOn
            · intro x hx
              have : 0 < x := by linarith [hx.1]
              positivity
          · intro x hx
            rw [norm_mul, hu'b x (by linarith [hx.1])]
            have := hvb x
            have h0 : 0 ≤ 1 / (2 * ‖b‖ * x ^ 2) := by positivity
            nlinarith
      _ = 1 / (2 * ‖b‖) * (1 / X - 1 / R) := by
          have : ∀ x ∈ Set.uIcc X R, HasDerivAt (fun y : ℝ => -(1 / (2 * ‖b‖)) / y)
              (1 / (2 * ‖b‖ * x ^ 2)) x := by
            intro x hx
            rw [hIcc] at hx
            have hx0 : x ≠ 0 := by linarith [hx.1]
            have h := ((hasDerivAt_id x).inv hx0).const_mul (-(1 / (2 * ‖b‖)))
            refine h.congr_deriv ?_
            simp only [id]
            first | (field_simp; done) | (field_simp; ring)
          rw [integral_eq_sub_of_hasDerivAt this (by
            apply ContinuousOn.intervalIntegrable
            rw [hIcc]
            apply ContinuousOn.div continuousOn_const
            · exact (continuous_const.mul (continuous_id.pow 2)).continuousOn
            · intro x hx
              have : 0 < x := by linarith [hx.1]
              positivity)]
          field_simp
          ring
      _ ≤ 1 / (2 * ‖b‖ * X) := by
          have h1 : 0 ≤ 1 / R := by positivity
          have h2 : 0 ≤ 1 / (2 * ‖b‖) := by positivity
          have : 1 / (2 * ‖b‖) * (1 / X - 1 / R) ≤ 1 / (2 * ‖b‖) * (1 / X) := by
            apply mul_le_mul_of_nonneg_left _ h2
            linarith
          calc _ ≤ 1 / (2 * ‖b‖) * (1 / X) := this
            _ = 1 / (2 * ‖b‖ * X) := by field_simp
  calc ‖u R * v R - u X * v X - ∫ x in X..R, u' x * v x‖
      ≤ ‖u R * v R - u X * v X‖ + ‖∫ x in X..R, u' x * v x‖ := norm_sub_le _ _
    _ ≤ 1 / (2 * ‖b‖ * R) + 1 / (2 * ‖b‖ * X) + 1 / (2 * ‖b‖ * X) := add_le_add hbd hI
    _ = 1 / (‖b‖ * X) + 1 / (2 * ‖b‖ * R) := by
        field_simp
        ring

/-- The regularised Fresnel integral is within `1/(πAX)` of `(π/b)^{1/2}`. -/
theorem regularised {A ε X : ℝ} (hA : 0 < A) (hε : 0 < ε) (hX : 0 < X) :
    ‖(∫ x in (-X)..X, Complex.exp (-bε A ε * (x : ℂ) ^ 2)) -
        (Real.pi / bε A ε) ^ ((1 : ℂ) / 2)‖ ≤ 1 / (Real.pi * A * X) := by
  set b := bε A ε with hbdef
  have hbre : 0 < b.re := by rw [hbdef, bε_re]; exact hε
  have hb0 : b ≠ 0 := bε_ne_zero hA
  have hnb : 2 * Real.pi * A ≤ ‖b‖ := norm_bε_ge hA
  have hnb0 : 0 < ‖b‖ := norm_pos_iff.2 hb0
  set f : ℝ → ℂ := fun x => Complex.exp (-b * (x : ℂ) ^ 2) with hf
  have hfi : Integrable f := integrable_cexp_neg_mul_sq hbre
  have hfc : Continuous f := by
    rw [hf]
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.pow 2))
  have hgauss : ∫ x : ℝ, f x = (Real.pi / b) ^ ((1 : ℂ) / 2) := by
    rw [hf]
    exact integral_gaussian_complex hbre
  have heven : ∀ x, f (-x) = f x := by
    intro x
    rw [hf]
    simp
  -- the right tail and its limit
  have htail : ∀ R, X ≤ R → ‖∫ x in X..R, f x‖ ≤ 1 / (‖b‖ * X) + 1 / (2 * ‖b‖ * R) :=
    fun R hR => tail_bound hb0 hX hR hbre.le
  have htend : Tendsto (fun R : ℝ => ∫ x in X..R, f x) atTop (𝓝 (∫ x in Set.Ioi X, f x)) :=
    intervalIntegral_tendsto_integral_Ioi X hfi.integrableOn tendsto_id
  have hIoi : ‖∫ x in Set.Ioi X, f x‖ ≤ 1 / (‖b‖ * X) := by
    have h1 : Tendsto (fun R : ℝ => 1 / (‖b‖ * X) + 1 / (2 * ‖b‖ * R)) atTop
        (𝓝 (1 / (‖b‖ * X) + 0)) := by
      apply tendsto_const_nhds.add
      have h2 : Tendsto (fun R : ℝ => 2 * ‖b‖ * R) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity) tendsto_id
      have h3 := h2.inv_tendsto_atTop
      refine h3.congr fun R => ?_
      simp [one_div]
    rw [add_zero] at h1
    exact le_of_tendsto_of_tendsto htend.norm h1
      (Filter.eventually_atTop.2 ⟨X, fun R hR => htail R hR⟩)
  -- the symmetric decomposition `∫_ℝ f = 2 ∫_{Ioi X} f + ∫_{-X}^{X} f`
  have hdecomp : ∫ x : ℝ, f x = 2 * (∫ x in Set.Ioi X, f x) + ∫ x in (-X)..X, f x := by
    have hsplit : ∀ R, X ≤ R →
        ∫ x in (-R)..R, f x = 2 * (∫ x in X..R, f x) + ∫ x in (-X)..X, f x := by
      intro R hR
      have hi : ∀ p q : ℝ, IntervalIntegrable f volume p q := fun p q => hfi.intervalIntegrable
      have h1 : ∫ x in (-R)..R, f x =
          (∫ x in (-R)..(-X), f x) + (∫ x in (-X)..X, f x) + ∫ x in X..R, f x := by
        rw [integral_add_adjacent_intervals (hi _ _) (hi _ _),
          integral_add_adjacent_intervals (hi _ _) (hi _ _)]
      have h2 : ∫ x in (-R)..(-X), f x = ∫ x in X..R, f x := by
        have := intervalIntegral.integral_comp_neg (a := X) (b := R) f
        rw [← this]
        apply integral_congr
        intro x _
        exact heven x
      rw [h1, h2]
      ring
    have hL : Tendsto (fun R : ℝ => ∫ x in (-R)..R, f x) atTop (𝓝 (∫ x : ℝ, f x)) :=
      intervalIntegral_tendsto_integral hfi tendsto_neg_atTop_atBot tendsto_id
    have hR : Tendsto (fun R : ℝ => 2 * (∫ x in X..R, f x) + ∫ x in (-X)..X, f x) atTop
        (𝓝 (2 * (∫ x in Set.Ioi X, f x) + ∫ x in (-X)..X, f x)) :=
      (htend.const_mul 2).add tendsto_const_nhds
    have hL' : Tendsto (fun R : ℝ => ∫ x in (-R)..R, f x) atTop
        (𝓝 (2 * (∫ x in Set.Ioi X, f x) + ∫ x in (-X)..X, f x)) := by
      refine hR.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop X] with R hR
      exact (hsplit R hR).symm
    exact tendsto_nhds_unique hL hL'
  -- conclude
  have heq : (∫ x in (-X)..X, f x) - (Real.pi / b) ^ ((1 : ℂ) / 2) =
      -(2 * ∫ x in Set.Ioi X, f x) := by
    rw [← hgauss, hdecomp]
    ring
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [heq, norm_neg, norm_mul, h2]
  calc 2 * ‖∫ x in Set.Ioi X, f x‖ ≤ 2 * (1 / (‖b‖ * X)) := by gcongr
    _ ≤ 2 * (1 / (2 * Real.pi * A * X)) := by
        gcongr
    _ = 1 / (Real.pi * A * X) := by
        first | (field_simp; done) | (field_simp; ring)

/-- The regularisation error: `‖∫_{-X}^{X} (exp(−b_ε x²) − e(Ax²))‖ ≤ 2εX³`. -/
theorem regularisation_error {A ε X : ℝ} (hε : 0 ≤ ε) (hX : 0 < X) :
    ‖(∫ x in (-X)..X, Complex.exp (-bε A ε * (x : ℂ) ^ 2)) - ∫ x in (-X)..X, e (A * x ^ 2)‖ ≤
      2 * ε * X ^ 3 := by
  have hc1 : Continuous fun x : ℝ => Complex.exp (-bε A ε * (x : ℂ) ^ 2) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.pow 2))
  have hc2 : Continuous fun x : ℝ => e (A * x ^ 2) := by
    unfold e
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_id.pow 2))))
  rw [← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
  have := norm_integral_le_of_norm_le_const (a := -X) (b := X) (C := ε * X ^ 2)
    (f := fun x => Complex.exp (-bε A ε * (x : ℂ) ^ 2) - e (A * x ^ 2)) (fun x hx => by
      rw [Set.uIoc_of_le (by linarith)] at hx
      rw [cexp_bε, ← sub_one_mul, norm_mul, norm_e, mul_one, ← Complex.ofReal_one,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have h1 : Real.exp (-ε * x ^ 2) ≤ 1 := by
        apply Real.exp_le_one_iff.2
        nlinarith [sq_nonneg x]
      have h2 : 1 - ε * x ^ 2 ≤ Real.exp (-ε * x ^ 2) := by
        have := Real.add_one_le_exp (-ε * x ^ 2)
        linarith
      have h3 : x ^ 2 ≤ X ^ 2 := by
        rw [sq_le_sq, abs_of_pos hX]
        rw [abs_le]
        exact ⟨by linarith [hx.1], hx.2⟩
      rw [abs_le]
      constructor
      · nlinarith
      · nlinarith)
  rw [show X - -X = 2 * X by ring, abs_of_pos (by linarith)] at this
  calc _ ≤ ε * X ^ 2 * (2 * X) := this
    _ = 2 * ε * X ^ 3 := by ring

/-- The limiting value `(π/(−2πiA))^{1/2} = e(1/8)/√(2A)`. -/
theorem limit_value {A : ℝ} (hA : 0 < A) :
    (Real.pi / bε A 0) ^ ((1 : ℂ) / 2) = e (1 / 8) / ((Real.sqrt (2 * A) : ℝ) : ℂ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set r : ℝ := 1 / (2 * A) with hr
  have hr0 : 0 < r := by positivity
  have hz : (Real.pi / bε A 0 : ℂ) = (r : ℂ) * Complex.I := by
    rw [div_eq_iff (bε_ne_zero hA), bε, hr]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    field_simp
    exact (div_self (by exact_mod_cast hA.ne' : (A : ℂ) ≠ 0)).symm
  rw [hz]
  have hz0 : (r : ℂ) * Complex.I ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast hr0.ne'
    · exact Complex.I_ne_zero
  rw [Complex.cpow_def_of_ne_zero hz0]
  have hlog : Complex.log ((r : ℂ) * Complex.I) =
      (Real.log r : ℂ) + (Real.pi / 2 : ℝ) * Complex.I := by
    rw [Complex.log, Complex.arg_real_mul _ hr0, Complex.arg_I, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  rw [hlog]
  have hsplit : ((Real.log r : ℂ) + (Real.pi / 2 : ℝ) * Complex.I) * (1 / 2) =
      ((Real.log r / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((1 / 8 : ℝ) : ℂ) := by
    push_cast
    ring
  have hexp1 : Complex.exp ((Real.log r / 2 : ℝ) : ℂ) = 1 / ((Real.sqrt (2 * A) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp]
    have h1 : Real.exp (Real.log r / 2) = Real.sqrt r := by
      symm
      rw [Real.sqrt_eq_iff_mul_self_eq hr0.le (Real.exp_pos _).le, ← Real.exp_add,
        show Real.log r / 2 + Real.log r / 2 = Real.log r by ring, Real.exp_log hr0]
    rw [h1, hr, Real.sqrt_div' _ (by positivity), Real.sqrt_one]
    push_cast
    rfl
  rw [hsplit, Complex.exp_add, hexp1]
  unfold e
  ring

end GK33

/-- **Graham–Kolesnik, Lemma 3.3** holds (with constant `1`). -/
theorem gk_lemma33_holds : gk_lemma33 := by
  refine ⟨1, fun A X hA hX => ?_⟩
  have hpi : (3 : ℝ) < Real.pi := BI.pi_gt_three'
  set L : ℂ := (Real.pi / GK33.bε A 0) ^ ((1 : ℂ) / 2) with hL
  rw [← GK33.limit_value hA]
  -- the bound for every `ε > 0`
  have hbound : ∀ ε : ℝ, 0 < ε →
      ‖(∫ x in (-X)..X, e (A * x ^ 2)) - L‖ ≤
        2 * ε * X ^ 3 + 1 / (Real.pi * A * X) +
          ‖(Real.pi / GK33.bε A ε) ^ ((1 : ℂ) / 2) - L‖ := by
    intro ε hε
    have h1 := GK33.regularisation_error (A := A) hε.le hX
    have h2 := GK33.regularised hA hε hX
    set I₁ := ∫ x in (-X)..X, e (A * x ^ 2)
    set I₂ := ∫ x in (-X)..X, Complex.exp (-GK33.bε A ε * (x : ℂ) ^ 2)
    set P := (Real.pi / GK33.bε A ε) ^ ((1 : ℂ) / 2)
    calc ‖I₁ - L‖ = ‖-(I₂ - I₁) + (I₂ - P) + (P - L)‖ := by congr 1; ring
      _ ≤ ‖-(I₂ - I₁)‖ + ‖I₂ - P‖ + ‖P - L‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ _ := by
          rw [norm_neg]
          gcongr
  -- the right-hand side tends to `1/(πAX)` as `ε → 0⁺`
  have hcont : Tendsto (fun ε : ℝ => (Real.pi / GK33.bε A ε) ^ ((1 : ℂ) / 2)) (𝓝 0) (𝓝 L) := by
    rw [hL]
    have hb : Continuous fun ε : ℝ => GK33.bε A ε := by
      unfold GK33.bε
      exact Complex.continuous_ofReal.sub continuous_const
    have hne : ∀ ε : ℝ, GK33.bε A ε ≠ 0 := fun ε => GK33.bε_ne_zero hA
    have hq : Continuous fun ε : ℝ => (Real.pi : ℂ) / GK33.bε A ε :=
      continuous_const.div hb hne
    have hslit : (Real.pi : ℂ) / GK33.bε A 0 ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      right
      have hz : (Real.pi / GK33.bε A 0 : ℂ) = ((1 / (2 * A) : ℝ) : ℂ) * Complex.I := by
        rw [div_eq_iff (GK33.bε_ne_zero hA), GK33.bε]
        push_cast
        ring_nf
        rw [Complex.I_sq]
        field_simp
        exact (div_self (by exact_mod_cast hA.ne' : (A : ℂ) ≠ 0)).symm
      rw [hz, Complex.mul_I_im, Complex.ofReal_re]
      positivity
    exact (continuousAt_cpow_const hslit).tendsto.comp (hq.tendsto 0)
  have hlim : Tendsto (fun ε : ℝ => 2 * ε * X ^ 3 + 1 / (Real.pi * A * X) +
      ‖(Real.pi / GK33.bε A ε) ^ ((1 : ℂ) / 2) - L‖) (𝓝[>] 0)
      (𝓝 (2 * 0 * X ^ 3 + 1 / (Real.pi * A * X) + ‖L - L‖)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply Tendsto.add
    · apply Tendsto.add
      · exact ((continuous_const.mul continuous_id).mul continuous_const).continuousAt.tendsto
      · exact tendsto_const_nhds
    · exact (hcont.sub tendsto_const_nhds).norm
  rw [sub_self, norm_zero, mul_zero, zero_mul, zero_add, add_zero] at hlim
  have hfinal : ‖(∫ x in (-X)..X, e (A * x ^ 2)) - L‖ ≤ 1 / (Real.pi * A * X) :=
    ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => hbound ε hε)
  calc _ ≤ 1 / (Real.pi * A * X) := hfinal
    _ ≤ 1 / (A * X) := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [mul_pos hA hX]

end LeanProofs.IntegerPoints
