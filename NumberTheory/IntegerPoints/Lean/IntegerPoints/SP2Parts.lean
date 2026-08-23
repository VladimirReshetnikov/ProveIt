import IntegerPoints.SP1Taylor

/-!
# Stationary phase, part 2: the integral `T₁ = ∫_a^b e(g(x)) r'(x)/x dx`

With `w(x) = r'(x)/(x g'(x))` we have `e(g) r'/x = w · (e∘g)'/(2πi)`, so on a piece
`[p, q]` not containing `0`,
`∫_p^q e(g) r'/x = (1/2πi)([w e(g)]_p^q − ∫_p^q w' e(g))`.
The bounds `|w| ≤ λ₃/(2λ₂)` and `|w'| ≤ λ₄/(6λ₂) + 3λ₃²/(4λ₂²)` come from `SP1Taylor`:
`w' = (Φ g' − r'(x r'' − r'))/(x g')²`.  The piece `[−ε, ε]` contributes at most `λ₃ε²`,
and `ε → 0` gives
`|T₁| ≤ (1/2π)(λ₃/λ₂ + (b − a)(λ₄/(6λ₂) + 3λ₃²/(4λ₂²)))`.
-/

open Real Finset intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace SP

/-- Interval integrability of a measurable `ℂ`-valued function bounded on the interval. -/
theorem intervalIntegrable_of_bounded_on_complex {f : ℝ → ℂ} (hf : Measurable f) {C p q : ℝ}
    (hb : ∀ x ∈ Set.uIcc p q, ‖f x‖ ≤ C) : IntervalIntegrable f volume p q := by
  refine ⟨?_, ?_⟩
  · refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne
      hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    apply hb
    rw [Set.mem_uIcc]
    exact Or.inl ⟨hx.1.le, hx.2⟩
  · refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne
      hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    apply hb
    rw [Set.mem_uIcc]
    exact Or.inr ⟨hx.1.le, hx.2⟩

/-- If `X ≤ K + c ε²` for all small `ε > 0`, then `X ≤ K`. -/
theorem le_of_forall_small {X K c ε₀ : ℝ} (hc : 0 ≤ c) (hε₀ : 0 < ε₀)
    (h : ∀ ε, 0 < ε → ε ≤ ε₀ → X ≤ K + c * ε ^ 2) : X ≤ K := by
  by_contra hcon
  push Not at hcon
  set d := X - K with hd
  have hd0 : 0 < d := by linarith
  set ε := min ε₀ (Real.sqrt (d / (2 * c + 1))) with hε
  have hs0 : 0 < Real.sqrt (d / (2 * c + 1)) := Real.sqrt_pos.2 (by positivity)
  have hε0 : 0 < ε := lt_min hε₀ hs0
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  have hε2 : ε ^ 2 ≤ d / (2 * c + 1) := by
    calc ε ^ 2 ≤ (Real.sqrt (d / (2 * c + 1))) ^ 2 :=
          pow_le_pow_left₀ hε0.le (min_le_right _ _) 2
      _ = d / (2 * c + 1) := Real.sq_sqrt (by positivity)
  have := h ε hε0 hεε₀
  have h2 : c * ε ^ 2 < d := by
    calc c * ε ^ 2 ≤ c * (d / (2 * c + 1)) := mul_le_mul_of_nonneg_left hε2 hc
      _ < d := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  linarith

namespace Data

variable (D : Data)

/-- The weight `w(x) = r'(x) / (x g'(x))`. -/
noncomputable def w (x : ℝ) : ℝ := D.r1 x / (x * D.g1 x)

/-- `w'(x) = (Φ(x) g'(x) − r'(x)(x r''(x) − r'(x))) / (x g'(x))²`. -/
noncomputable def w' (x : ℝ) : ℝ :=
  (D.Φ x * D.g1 x - D.r1 x * (x * D.r2 x - D.r1 x)) / (x * D.g1 x) ^ 2

theorem hasDerivAt_w {x : ℝ} (hx0 : x ≠ 0) (hg : D.g1 x ≠ 0) : HasDerivAt D.w (D.w' x) x := by
  unfold w
  have hden : x * D.g1 x ≠ 0 := mul_ne_zero hx0 hg
  have hd : HasDerivAt (fun y => y * D.g1 y) (1 * D.g1 x + x * D.g2 x) x :=
    (hasDerivAt_id' x).mul (D.hasDerivAt_g1 x)
  have := (D.hasDerivAt_r1 x).div hd hden
  refine this.congr_deriv ?_
  unfold w' Φ r1 r2
  field_simp
  ring

theorem abs_w_le {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) (hx0 : x ≠ 0) :
    |D.w x| ≤ D.lam₃ / (2 * D.lam₂) := by
  unfold w
  have hl2 := D.hlam₂
  have hl3 := D.hlam₃
  have h1 := D.abs_r1_le hx
  have h2 := D.abs_g1_ge hx
  have hx2 : 0 < x ^ 2 := by positivity
  have hxg : D.lam₂ * x ^ 2 ≤ |x * D.g1 x| := by
    rw [abs_mul, ← sq_abs x]
    have := mul_le_mul_of_nonneg_left h2 (abs_nonneg x)
    nlinarith [abs_nonneg x]
  have hpos : 0 < |x * D.g1 x| := by
    have : 0 < D.lam₂ * x ^ 2 := by positivity
    linarith
  rw [abs_div, div_le_div_iff₀ hpos (by positivity)]
  calc |D.r1 x| * (2 * D.lam₂) ≤ (D.lam₃ * x ^ 2 / 2) * (2 * D.lam₂) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = D.lam₃ * (D.lam₂ * x ^ 2) := by ring
    _ ≤ D.lam₃ * |x * D.g1 x| := mul_le_mul_of_nonneg_left hxg D.hlam₃.le

/-- `B₂ = λ₄/(6λ₂) + 3λ₃²/(4λ₂²)`. -/
noncomputable def B₂ : ℝ := D.lam₄ / (6 * D.lam₂) + 3 * D.lam₃ ^ 2 / (4 * D.lam₂ ^ 2)

theorem B₂_nonneg : 0 ≤ D.B₂ := by
  unfold B₂
  have := D.hlam₂
  have := D.hlam₃
  have := D.hlam₄
  positivity

theorem abs_w'_le {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) (hx0 : x ≠ 0) : |D.w' x| ≤ D.B₂ := by
  unfold w' B₂
  have hl2 := D.hlam₂
  have hl3 := D.hlam₃
  have hl4 := D.hlam₄
  have hx4 : x ^ 4 = |x| ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, sq_abs]
  have hΦ := D.abs_Φ_le hx
  have hr1 := D.abs_r1_le hx
  have hxr := D.abs_xr2_sub_r1_le hx
  have hg := D.abs_g1_ge hx
  have hx2 : 0 < x ^ 2 := by positivity
  have hxa : 0 < |x| := abs_pos.2 hx0
  have hden : D.lam₂ ^ 2 * x ^ 4 ≤ (x * D.g1 x) ^ 2 := by
    rw [← sq_abs (x * D.g1 x), abs_mul]
    have h1 : D.lam₂ * |x| * |x| ≤ |x| * |D.g1 x| := by
      have := mul_le_mul_of_nonneg_left hg (abs_nonneg x)
      linarith
    have h2 : 0 ≤ D.lam₂ * |x| * |x| := by positivity
    calc D.lam₂ ^ 2 * x ^ 4 = (D.lam₂ * |x| * |x|) ^ 2 := by rw [hx4]; ring
      _ ≤ (|x| * |D.g1 x|) ^ 2 := pow_le_pow_left₀ h2 h1 2
  have hdenpos : 0 < (x * D.g1 x) ^ 2 := by
    have : 0 < D.lam₂ ^ 2 * x ^ 4 := by have := D.hlam₂; positivity
    linarith
  rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
  -- numerator bound
  have hnum : |D.Φ x * D.g1 x - D.r1 x * (x * D.r2 x - D.r1 x)| ≤
      D.lam₄ * |x| ^ 3 / 6 * |D.g1 x| + D.lam₃ * x ^ 2 / 2 * (3 * D.lam₃ * x ^ 2 / 2) := by
    calc |D.Φ x * D.g1 x - D.r1 x * (x * D.r2 x - D.r1 x)|
        ≤ |D.Φ x * D.g1 x| + |D.r1 x * (x * D.r2 x - D.r1 x)| := abs_sub _ _
      _ = |D.Φ x| * |D.g1 x| + |D.r1 x| * |x * D.r2 x - D.r1 x| := by rw [abs_mul, abs_mul]
      _ ≤ D.lam₄ * |x| ^ 3 / 6 * |D.g1 x| + D.lam₃ * x ^ 2 / 2 * (3 * D.lam₃ * x ^ 2 / 2) := by
          gcongr
  refine hnum.trans ?_
  -- `|g'| ≤ (x g')² / (λ₂ |x|³)` is awkward; instead compare term by term
  have hg1sq : |D.g1 x| * (D.lam₂ * |x|) ≤ |D.g1 x| ^ 2 := by
    have := mul_le_mul_of_nonneg_left hg (abs_nonneg (D.g1 x))
    linarith
  have e1 : D.lam₄ * |x| ^ 3 / 6 * |D.g1 x| ≤ D.lam₄ / (6 * D.lam₂) * (x * D.g1 x) ^ 2 := by
    rw [← sq_abs (x * D.g1 x), abs_mul, mul_pow]
    have key : D.lam₂ * (|x| ^ 3 * |D.g1 x|) ≤ |x| ^ 2 * |D.g1 x| ^ 2 := by
      have := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ |x| ^ 2 * |D.g1 x|)
      nlinarith
    calc D.lam₄ * |x| ^ 3 / 6 * |D.g1 x| =
          D.lam₄ / (6 * D.lam₂) * (D.lam₂ * (|x| ^ 3 * |D.g1 x|)) := by
          first | (field_simp; done) | (field_simp; ring)
      _ ≤ D.lam₄ / (6 * D.lam₂) * (|x| ^ 2 * |D.g1 x| ^ 2) :=
          mul_le_mul_of_nonneg_left key (by positivity)
  have e2 : D.lam₃ * x ^ 2 / 2 * (3 * D.lam₃ * x ^ 2 / 2) ≤
      3 * D.lam₃ ^ 2 / (4 * D.lam₂ ^ 2) * (x * D.g1 x) ^ 2 := by
    calc D.lam₃ * x ^ 2 / 2 * (3 * D.lam₃ * x ^ 2 / 2) =
          3 * D.lam₃ ^ 2 / (4 * D.lam₂ ^ 2) * (D.lam₂ ^ 2 * x ^ 4) := by
          first | (field_simp; done) | (field_simp; ring)
      _ ≤ 3 * D.lam₃ ^ 2 / (4 * D.lam₂ ^ 2) * (x * D.g1 x) ^ 2 :=
          mul_le_mul_of_nonneg_left hden (by positivity)
  calc _ ≤ D.lam₄ / (6 * D.lam₂) * (x * D.g1 x) ^ 2 +
        3 * D.lam₃ ^ 2 / (4 * D.lam₂ ^ 2) * (x * D.g1 x) ^ 2 := add_le_add e1 e2
    _ = _ := by ring

theorem continuousOn_w' {p q : ℝ} (hpq : p ≤ q) (h0 : (0 : ℝ) ∉ Set.Icc p q)
    (hsub : Set.Icc p q ⊆ Set.Icc D.a D.b) : ContinuousOn D.w' (Set.Icc p q) := by
  unfold w'
  apply ContinuousOn.div
  · exact ((D.continuous_Φ.mul D.continuous_g1).sub
      (D.continuous_r1.mul ((continuous_id.mul D.continuous_r2).sub D.continuous_r1))).continuousOn
  · exact ((continuous_id.mul D.continuous_g1).pow 2).continuousOn
  · intro x hx
    have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
    exact pow_ne_zero 2 (mul_ne_zero hx0 (D.g1_ne_zero (hsub hx) hx0))

/-- `T₁` on a piece `[p, q] ⊆ [a, b]` with `0 ∉ [p, q]`. -/
theorem T1_piece {p q : ℝ} (hpq : p ≤ q) (h0 : (0 : ℝ) ∉ Set.Icc p q)
    (hsub : Set.Icc p q ⊆ Set.Icc D.a D.b) :
    ‖∫ x in p..q, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)‖ ≤
      1 / (2 * π) * (D.lam₃ / D.lam₂ + (q - p) * D.B₂) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hIcc : Set.uIcc p q = Set.Icc p q := Set.uIcc_of_le hpq
  have hne : ∀ x ∈ Set.Icc p q, x ≠ 0 ∧ D.g1 x ≠ 0 := fun x hx =>
    ⟨fun h => h0 (h ▸ hx), D.g1_ne_zero (hsub hx) (fun h => h0 (h ▸ hx))⟩
  -- integration by parts with `u = w`, `v = e ∘ g`
  have hu : ∀ x ∈ Set.uIcc p q, HasDerivAt (fun x => ((D.w x : ℝ) : ℂ)) ((D.w' x : ℝ) : ℂ) x := by
    intro x hx
    rw [hIcc] at hx
    exact (D.hasDerivAt_w (hne x hx).1 (hne x hx).2).ofReal_comp
  have hv : ∀ x ∈ Set.uIcc p q,
      HasDerivAt (fun x => e (D.g x)) (2 * π * Complex.I * D.g1 x * e (D.g x)) x :=
    fun x _ => PS.hasDerivAt_e_comp (D.hasDerivAt_g x)
  have hu'i : IntervalIntegrable (fun x => ((D.w' x : ℝ) : ℂ)) volume p q := by
    apply ContinuousOn.intervalIntegrable
    rw [hIcc]
    exact Complex.continuous_ofReal.comp_continuousOn (D.continuousOn_w' hpq h0 hsub)
  have hv'i : IntervalIntegrable (fun x => 2 * π * Complex.I * D.g1 x * e (D.g x)) volume p q :=
    ((continuous_const.mul (Complex.continuous_ofReal.comp D.continuous_g1)).mul
      (PS.continuous_e_comp D.continuous_g)).intervalIntegrable _ _
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'i hv'i
  have hI : (2 * π * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hL : ∫ x in p..q, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ) =
      (1 / (2 * π * Complex.I)) * ∫ x in p..q, ((D.w x : ℝ) : ℂ) *
        (2 * π * Complex.I * D.g1 x * e (D.g x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro x hx
    rw [hIcc] at hx
    simp only
    unfold w
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (hne x hx).1
    have hg0 : (D.g1 x : ℂ) ≠ 0 := by exact_mod_cast (hne x hx).2
    push_cast
    first | (field_simp; done) | (field_simp; ring)
  rw [hL, h, norm_mul, norm_div, norm_one, PS.norm_two_pi_I]
  have hwq := D.abs_w_le (hsub ⟨hpq, le_rfl⟩) (hne q ⟨hpq, le_rfl⟩).1
  have hwp := D.abs_w_le (hsub ⟨le_rfl, hpq⟩) (hne p ⟨le_rfl, hpq⟩).1
  have hint : ‖∫ x in p..q, ((D.w' x : ℝ) : ℂ) * e (D.g x)‖ ≤ (q - p) * D.B₂ := by
    have := norm_integral_le_of_norm_le_const (a := p) (b := q) (C := D.B₂)
      (f := fun x => ((D.w' x : ℝ) : ℂ) * e (D.g x)) (fun x hx => by
        rw [Set.uIoc_of_le hpq] at hx
        rw [norm_mul, PS.norm_e_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact D.abs_w'_le (hsub ⟨hx.1.le, hx.2⟩) (hne x ⟨hx.1.le, hx.2⟩).1)
    rw [abs_of_nonneg (by linarith)] at this
    linarith
  have hB : ‖((D.w q : ℝ) : ℂ) * e (D.g q) - ((D.w p : ℝ) : ℂ) * e (D.g p) -
      ∫ x in p..q, ((D.w' x : ℝ) : ℂ) * e (D.g x)‖ ≤ D.lam₃ / D.lam₂ + (q - p) * D.B₂ := by
    calc _ ≤ ‖((D.w q : ℝ) : ℂ) * e (D.g q) - ((D.w p : ℝ) : ℂ) * e (D.g p)‖ +
          ‖∫ x in p..q, ((D.w' x : ℝ) : ℂ) * e (D.g x)‖ := norm_sub_le _ _
      _ ≤ (‖((D.w q : ℝ) : ℂ) * e (D.g q)‖ + ‖((D.w p : ℝ) : ℂ) * e (D.g p)‖) +
          (q - p) * D.B₂ := by gcongr; exact norm_sub_le _ _
      _ ≤ (D.lam₃ / (2 * D.lam₂) + D.lam₃ / (2 * D.lam₂)) + (q - p) * D.B₂ := by
          gcongr
          · rw [norm_mul, PS.norm_e_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
            exact hwq
          · rw [norm_mul, PS.norm_e_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
            exact hwp
      _ = D.lam₃ / D.lam₂ + (q - p) * D.B₂ := by ring
  calc 1 / (2 * π) * ‖((D.w q : ℝ) : ℂ) * e (D.g q) - ((D.w p : ℝ) : ℂ) * e (D.g p) -
        ∫ x in p..q, ((D.w' x : ℝ) : ℂ) * e (D.g x)‖
      ≤ 1 / (2 * π) * (D.lam₃ / D.lam₂ + (q - p) * D.B₂) := by gcongr

theorem measurable_T1_integrand : Measurable fun x => e (D.g x) * ((D.r1 x / x : ℝ) : ℂ) :=
  (PS.continuous_e_comp D.continuous_g).measurable.mul
    (Complex.measurable_ofReal.comp (D.continuous_r1.measurable.div measurable_id))

theorem norm_T1_integrand_le {x : ℝ} (hx : x ∈ Set.Icc D.a D.b) :
    ‖e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)‖ ≤ D.lam₃ * |x| / 2 := by
  rw [norm_mul, PS.norm_e_one, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rcases eq_or_ne x 0 with h | h
  · rw [h]
    simp
  · rw [abs_div, div_le_iff₀ (abs_pos.2 h)]
    have := D.abs_r1_le hx
    rw [← sq_abs] at this
    nlinarith [abs_nonneg x]

/-- **The bound on `T₁`.** -/
theorem T1_bound :
    ‖∫ x in D.a..D.b, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)‖ ≤
      1 / (2 * π) * (2 * D.lam₃ / D.lam₂ + (D.b - D.a) * D.B₂) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  set M : ℝ := max (-D.a) D.b with hM
  have hM0 : 0 < M := lt_max_of_lt_right D.hb
  have habsM : ∀ x ∈ Set.Icc D.a D.b, |x| ≤ M := by
    intro x hx
    rw [abs_le]
    constructor
    · have : -D.a ≤ M := le_max_left _ _
      linarith [hx.1]
    · exact hx.2.trans (le_max_right _ _)
  have hint : ∀ p q : ℝ, p ∈ Set.Icc D.a D.b → q ∈ Set.Icc D.a D.b →
      IntervalIntegrable (fun x => e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)) volume p q := by
    intro p q hp hq
    apply intervalIntegrable_of_bounded_on_complex D.measurable_T1_integrand
      (C := D.lam₃ * M / 2)
    intro x hx
    have hx' : x ∈ Set.Icc D.a D.b := by
      rw [Set.mem_uIcc] at hx
      rcases hx with hx | hx
      · exact ⟨hp.1.trans hx.1, hx.2.trans hq.2⟩
      · exact ⟨hq.1.trans hx.1, hx.2.trans hp.2⟩
    refine (D.norm_T1_integrand_le hx').trans ?_
    have := habsM x hx'
    have := D.hlam₃
    nlinarith
  set ε₀ : ℝ := min (-D.a) D.b with hε₀
  have hε₀0 : 0 < ε₀ := lt_min (by linarith [D.ha]) D.hb
  apply le_of_forall_small (c := D.lam₃) D.hlam₃.le hε₀0
  intro ε hε hεε₀
  have hεa : D.a ≤ -ε := by
    have : ε ≤ -D.a := hεε₀.trans (min_le_left _ _)
    linarith
  have hεb : ε ≤ D.b := hεε₀.trans (min_le_right _ _)
  have hma : -ε ∈ Set.Icc D.a D.b := ⟨hεa, by linarith⟩
  have hme : ε ∈ Set.Icc D.a D.b := ⟨by linarith, hεb⟩
  have hmb : D.b ∈ Set.Icc D.a D.b := ⟨D.ha.le.trans D.hb.le, le_rfl⟩
  have hmaa : D.a ∈ Set.Icc D.a D.b := ⟨le_rfl, D.ha.le.trans D.hb.le⟩
  rw [← integral_add_adjacent_intervals (hint _ _ hmaa hma) (hint _ _ hma hmb),
    ← integral_add_adjacent_intervals (hint _ _ hma hme) (hint _ _ hme hmb)]
  have h1 := D.T1_piece (p := D.a) (q := -ε) hεa (fun h => by linarith [h.2])
    (Set.Icc_subset_Icc le_rfl (by linarith))
  have h3 := D.T1_piece (p := ε) (q := D.b) hεb (fun h => by linarith [h.1])
    (Set.Icc_subset_Icc (by linarith) le_rfl)
  have h2 : ‖∫ x in (-ε)..ε, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)‖ ≤ D.lam₃ * ε ^ 2 := by
    have := norm_integral_le_of_norm_le_const (a := -ε) (b := ε) (C := D.lam₃ * ε / 2)
      (f := fun x => e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)) (fun x hx => by
        rw [Set.uIoc_of_le (by linarith)] at hx
        have hx' : x ∈ Set.Icc D.a D.b := ⟨by linarith [hx.1], by linarith [hx.2]⟩
        refine (D.norm_T1_integrand_le hx').trans ?_
        have : |x| ≤ ε := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
        have := D.hlam₃
        nlinarith)
    rw [abs_of_nonneg (by linarith)] at this
    linarith
  have hB := D.B₂_nonneg
  calc ‖(∫ x in D.a..(-ε), e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)) +
        ((∫ x in (-ε)..ε, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)) +
          ∫ x in ε..D.b, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ))‖
      ≤ ‖∫ x in D.a..(-ε), e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)‖ +
        (‖∫ x in (-ε)..ε, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)‖ +
          ‖∫ x in ε..D.b, e (D.g x) * ((D.r1 x / x : ℝ) : ℂ)‖) := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 1 / (2 * π) * (D.lam₃ / D.lam₂ + (-ε - D.a) * D.B₂) +
        (D.lam₃ * ε ^ 2 + 1 / (2 * π) * (D.lam₃ / D.lam₂ + (D.b - ε) * D.B₂)) :=
        add_le_add h1 (add_le_add h2 h3)
    _ ≤ 1 / (2 * π) * (2 * D.lam₃ / D.lam₂ + (D.b - D.a) * D.B₂) + D.lam₃ * ε ^ 2 := by
        have h4 : 1 / (2 * π) * (D.lam₃ / D.lam₂ + (-ε - D.a) * D.B₂) +
            1 / (2 * π) * (D.lam₃ / D.lam₂ + (D.b - ε) * D.B₂) =
            1 / (2 * π) * (2 * D.lam₃ / D.lam₂ + (D.b - D.a) * D.B₂) -
              1 / (2 * π) * (2 * ε * D.B₂) := by ring
        have h5 : 0 ≤ 1 / (2 * π) * (2 * ε * D.B₂) := by positivity
        linarith

end Data

end SP

end LeanProofs.IntegerPoints
