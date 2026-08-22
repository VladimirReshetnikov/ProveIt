import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma


/-!
# The sine integral and the Dirichlet integral

`Si y = ∫₀^y sin v / v dv`.  We prove

* the tail bound `|Si y' - Si y| ≤ 2 / y` for `0 < y ≤ y'` (integration by
  parts),
* `|Si y| ≤ 3` for `y ≥ 0`, and `Si (-y) = -Si y`,
* the **Dirichlet integral** `Si y → π/2` as `y → ∞`, via the Dirichlet-kernel
  identity `∫₀^π sin((n+½)t) / (2 sin(t/2)) dt = π/2` and the Riemann–Lebesgue
  lemma applied to the bounded function `1/t - 1/(2 sin(t/2))`,
* hence `|Si y - π/2| ≤ 2 / y` for `y > 0`.

These are the analytic inputs for the truncated Perron formula
(Zhai–Cao, Lemma 2).
-/

open Real MeasureTheory intervalIntegral Filter Topology
open scoped FourierTransform

namespace LeanProofs.IntegerPoints

namespace SineIntegral

/-- The integrand `sin v / v` (equal to `0` at `v = 0` by Lean's convention). -/
noncomputable def sinc (v : ℝ) : ℝ := Real.sin v / v

/-- The sine integral `Si y = ∫₀^y sin v / v dv`. -/
noncomputable def Si (y : ℝ) : ℝ := ∫ v in (0 : ℝ)..y, sinc v

theorem abs_sinc_le_one (v : ℝ) : |sinc v| ≤ 1 := by
  unfold sinc
  rcases eq_or_ne v 0 with h | h
  · simp [h]
  · rw [abs_div, div_le_one (abs_pos.2 h)]
    exact Real.abs_sin_le_abs

theorem continuous_sinc_on (s : Set ℝ) (hs : (0 : ℝ) ∉ s) : ContinuousOn sinc s :=
  Real.continuous_sin.continuousOn.div continuousOn_id fun x hx => fun h => hs (h ▸ hx)

theorem measurable_sinc : Measurable sinc :=
  Real.measurable_sin.div measurable_id

theorem intervalIntegrable_sinc (a b : ℝ) : IntervalIntegrable sinc volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => (1 : ℝ)) intervalIntegrable_const
    measurable_sinc.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun v => abs_sinc_le_one v

theorem Si_zero : Si 0 = 0 := by simp [Si]

theorem Si_neg (y : ℝ) : Si (-y) = -Si y := by
  unfold Si
  have : ∀ v, sinc (-v) = sinc v := by
    intro v
    unfold sinc
    rw [Real.sin_neg, neg_div_neg_eq]
  have h1 : ∫ v in (0 : ℝ)..y, sinc (-v) = ∫ v in (-y)..(-0), sinc v :=
    intervalIntegral.integral_comp_neg sinc
  rw [neg_zero] at h1
  have h2 : ∫ v in (0 : ℝ)..y, sinc (-v) = ∫ v in (0 : ℝ)..y, sinc v :=
    intervalIntegral.integral_congr fun v _ => this v
  rw [intervalIntegral.integral_symm (-y) 0, ← h1, h2]

/-- `|Si y| ≤ |y|`. -/
theorem abs_Si_le (y : ℝ) : |Si y| ≤ |y| := by
  unfold Si
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := y) (C := 1)
    (f := sinc) fun v _ => by rw [Real.norm_eq_abs]; exact abs_sinc_le_one v
  simpa [Real.norm_eq_abs] using this

/-- Integration by parts: for `0 < x ≤ y`,
`∫_x^y sin v / v dv = cos x / x - cos y / y - ∫_x^y cos v / v² dv`. -/
theorem integral_sinc_eq (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    ∫ v in x..y, sinc v = Real.cos x / x - Real.cos y / y - ∫ v in x..y, Real.cos v / v ^ 2 := by
  have hpos : ∀ v ∈ Set.uIcc x y, 0 < v := by
    intro v hv
    rw [Set.uIcc_of_le hxy] at hv
    exact lt_of_lt_of_le hx hv.1
  have hu : ∀ v ∈ Set.uIcc x y, HasDerivAt (fun v : ℝ => v⁻¹) (-(v ^ 2)⁻¹) v := by
    intro v hv
    exact hasDerivAt_inv (hpos v hv).ne'
  have hv : ∀ v ∈ Set.uIcc x y, HasDerivAt (-Real.cos) (Real.sin v) v := by
    intro v _
    have h := (Real.hasDerivAt_cos v).neg
    rw [neg_neg] at h
    first
      | exact h
      | (convert h using 2)
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (by
      refine ContinuousOn.intervalIntegrable ?_
      exact ((continuousOn_pow 2).inv₀ fun v hv => (pow_pos (hpos v hv) 2).ne').neg)
    (Real.continuous_sin.intervalIntegrable _ _)
  have e1 : ∀ v, v⁻¹ * Real.sin v = sinc v := fun v => by rw [sinc, div_eq_inv_mul]
  simp_rw [e1] at key
  rw [key]
  have e2 : ∫ v in x..y, -(v ^ 2)⁻¹ * (-Real.cos) v = ∫ v in x..y, Real.cos v / v ^ 2 := by
    refine intervalIntegral.integral_congr fun v _ => ?_
    simp only [Pi.neg_apply]
    rw [div_eq_mul_inv]
    ring
  rw [e2]
  simp only [Pi.neg_apply]
  ring

/-- The tail bound `|Si y' - Si y| ≤ 2 / y` for `0 < y ≤ y'`. -/
theorem abs_Si_sub_le (y y' : ℝ) (hy : 0 < y) (hyy' : y ≤ y') : |Si y' - Si y| ≤ 2 / y := by
  have hsplit : Si y' - Si y = ∫ v in y..y', sinc v := by
    unfold Si
    rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_sinc 0 y)
      (intervalIntegrable_sinc y y')]
    ring
  rw [hsplit, integral_sinc_eq y y' hy hyy']
  have hy' : 0 < y' := lt_of_lt_of_le hy hyy'
  have h1 : |Real.cos y / y| ≤ 1 / y := by
    rw [abs_div, abs_of_pos hy]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hy.le
  have h2 : |Real.cos y' / y'| ≤ 1 / y' := by
    rw [abs_div, abs_of_pos hy']
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hy'.le
  have hpos : ∀ v ∈ Set.uIcc y y', 0 < v := by
    intro v hv
    rw [Set.uIcc_of_le hyy'] at hv
    exact lt_of_lt_of_le hy hv.1
  have hint : ∫ v in y..y', (v ^ 2)⁻¹ = 1 / y - 1 / y' := by
    have hF : ∀ v ∈ Set.uIcc y y', HasDerivAt (-fun v : ℝ => v⁻¹) ((v ^ 2)⁻¹) v := by
      intro v hv
      have h := (hasDerivAt_inv (hpos v hv).ne').neg
      rw [neg_neg] at h
      first
        | exact h
        | (convert h using 2)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF]
    · simp only [Pi.neg_apply]
      ring
    · refine ContinuousOn.intervalIntegrable ?_
      exact (continuousOn_pow 2).inv₀ fun v hv => (pow_pos (hpos v hv) 2).ne'
  have h3 : |∫ v in y..y', Real.cos v / v ^ 2| ≤ 1 / y - 1 / y' := by
    rw [← hint, ← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le hyy' ?_ ?_
    · refine Filter.Eventually.of_forall fun v hv => ?_
      have hv0 : 0 < v := lt_of_lt_of_le hy hv.1.le
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hv0 2), div_eq_mul_inv]
      calc |Real.cos v| * (v ^ 2)⁻¹ ≤ 1 * (v ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)
        _ = (v ^ 2)⁻¹ := one_mul _
    · refine ContinuousOn.intervalIntegrable ?_
      exact (continuousOn_pow 2).inv₀ fun v hv => (pow_pos (hpos v hv) 2).ne'
  have h4 : 1 / y' ≤ 1 / y := one_div_le_one_div_of_le hy hyy'
  calc |Real.cos y / y - Real.cos y' / y' - ∫ v in y..y', Real.cos v / v ^ 2|
      ≤ |Real.cos y / y - Real.cos y' / y'| + |∫ v in y..y', Real.cos v / v ^ 2| :=
        abs_sub _ _
    _ ≤ (|Real.cos y / y| + |Real.cos y' / y'|) + |∫ v in y..y', Real.cos v / v ^ 2| := by
        gcongr
        exact abs_sub _ _
    _ ≤ (1 / y + 1 / y') + (1 / y - 1 / y') := by gcongr
    _ = 2 / y := by ring

/-- `|Si y| ≤ 3` for `y ≥ 0`. -/
theorem abs_Si_le_three (y : ℝ) (hy : 0 ≤ y) : |Si y| ≤ 3 := by
  rcases le_or_gt y 2 with h | h
  · have := abs_Si_le y
    rw [abs_of_nonneg hy] at this
    linarith
  · have h1 := abs_Si_sub_le 2 y (by norm_num) h.le
    have h2 := abs_Si_le 2
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
    calc |Si y| = |(Si y - Si 2) + Si 2| := by congr 1; ring
      _ ≤ |Si y - Si 2| + |Si 2| := abs_add_le _ _
      _ ≤ 2 / 2 + 2 := add_le_add h1 h2
      _ = 3 := by norm_num

/-! ### The Dirichlet kernel -/

/-- `2 sin(t/2) (1/2 + Σ_{k<n} cos((k+1)t)) = sin((n+1/2) t)`. -/
theorem dirichlet_kernel (n : ℕ) (t : ℝ) :
    2 * Real.sin (t / 2) * (1 / 2 + ∑ k ∈ Finset.range n, Real.cos ((k + 1) * t)) =
      Real.sin ((n + 1 / 2) * t) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, Nat.cast_zero, zero_add]
    rw [show (1 / 2 : ℝ) * t = t / 2 by ring]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := Real.two_mul_sin_mul_cos (t / 2) ((n + 1) * t)
    have e1 : t / 2 - (n + 1) * t = -((n + 1 / 2) * t) := by ring
    have e2 : t / 2 + (n + 1) * t = ((n + 1 : ℕ) + 1 / 2) * t := by push_cast; ring
    rw [e1, Real.sin_neg, e2] at h
    calc 2 * Real.sin (t / 2) *
          (1 / 2 + (∑ k ∈ Finset.range n, Real.cos ((k + 1) * t) + Real.cos ((n + 1) * t)))
        = 2 * Real.sin (t / 2) * (1 / 2 + ∑ k ∈ Finset.range n, Real.cos ((k + 1) * t)) +
            2 * Real.sin (t / 2) * Real.cos ((n + 1) * t) := by ring
      _ = Real.sin ((n + 1 / 2) * t) +
            (-Real.sin ((n + 1 / 2) * t) + Real.sin (((n + 1 : ℕ) + 1 / 2) * t)) := by rw [ih, h]
      _ = Real.sin (((n + 1 : ℕ) + 1 / 2) * t) := by ring

/-- The Dirichlet kernel `D_n(t) = 1/2 + Σ_{k<n} cos((k+1)t)`. -/
noncomputable def D (n : ℕ) (t : ℝ) : ℝ := 1 / 2 + ∑ k ∈ Finset.range n, Real.cos ((k + 1) * t)

theorem continuous_D (n : ℕ) : Continuous (D n) := by
  unfold D
  fun_prop

/-- `∫₀^π D_n(t) dt = π/2`. -/
theorem integral_D (n : ℕ) : ∫ t in (0 : ℝ)..π, D n t = π / 2 := by
  unfold D
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((continuous_finset_sum _ fun k _ => by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_finsetSum
      (f := fun (k : ℕ) (t : ℝ) => Real.cos ((k + 1) * t))
      (fun k _ => (by fun_prop : Continuous fun t : ℝ => Real.cos ((k + 1) * t)).intervalIntegrable _ _)]
  have hz : ∀ k ∈ Finset.range n, ∫ t in (0 : ℝ)..π, Real.cos ((k + 1) * t) = 0 := by
    intro k _
    have hc : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun t => Real.cos t) hc, integral_cos, mul_zero,
      Real.sin_zero, sub_zero, show ((k : ℝ) + 1) * π = ((k + 1 : ℕ) : ℝ) * π by push_cast; ring,
      Real.sin_nat_mul_pi, smul_zero]
  rw [Finset.sum_eq_zero hz]
  simp only [sub_zero, add_zero, smul_eq_mul]
  ring

/-! ### The bounded function `1/t - 1/(2 sin(t/2))` -/

/-- `g(t) = 1/t - 1/(2 sin(t/2))`. -/
noncomputable def g (t : ℝ) : ℝ := 1 / t - 1 / (2 * Real.sin (t / 2))

theorem measurable_g : Measurable g := by
  unfold g
  fun_prop

theorem g_zero : g 0 = 0 := by simp [g]

/-- `|g(t)| ≤ 2` on `[0, π]`. -/
theorem abs_g_le (t : ℝ) (ht : t ∈ Set.Icc 0 π) : |g t| ≤ 2 := by
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0, g_zero, abs_zero]
    norm_num
  have hs : 0 < Real.sin (t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [ht.2, Real.pi_pos])
  rcases le_or_gt t 2 with h2 | h2
  · -- small `t`: Taylor bound
    set x := t / 2 with hx
    have hx0 : 0 < x := by rw [hx]; linarith
    have hx1 : x ≤ 1 := by rw [hx]; linarith
    have hb := Real.sin_bound (x := x) (by rw [abs_of_pos hx0]; exact hx1)
    rw [abs_of_pos hx0] at hb
    have hx5 : x ^ 5 ≤ x ^ 3 := pow_le_pow_of_le_one hx0.le hx1 (by norm_num)
    have hdiff : x - Real.sin x ≤ x ^ 3 / 5 := by
      have := (abs_le.1 hb).1
      nlinarith
    have hdiff0 : 0 ≤ x - Real.sin x := by linarith [Real.sin_le hx0.le]
    have hsin : 2 / π * x ≤ Real.sin x :=
      Real.mul_le_sin hx0.le (by linarith [Real.two_le_pi])
    have ht2 : t = 2 * x := by rw [hx]; ring
    have hg : g t = -((x - Real.sin x) / (t * Real.sin x)) := by
      rw [g, ← hx, ht2]
      field_simp
      ring
    rw [hg, abs_neg, abs_of_nonneg (div_nonneg hdiff0 (by positivity))]
    have hden : 2 * x * (2 / π * x) ≤ t * Real.sin x := by
      rw [ht2]
      exact mul_le_mul_of_nonneg_left hsin (by positivity)
    calc (x - Real.sin x) / (t * Real.sin x) ≤ (x ^ 3 / 5) / (t * Real.sin x) :=
          div_le_div_of_nonneg_right hdiff (by positivity)
      _ ≤ (x ^ 3 / 5) / (2 * x * (2 / π * x)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = π * x / 20 := by field_simp; ring
      _ ≤ 2 := by nlinarith [Real.pi_le_four]
  · -- `t ∈ [2, π]`
    have hsin1 : 2 / π ≤ Real.sin (t / 2) := by
      have h1 : 2 / π * 1 ≤ Real.sin 1 :=
        Real.mul_le_sin (by norm_num) (by linarith [Real.two_le_pi])
      have h2 : Real.sin 1 ≤ Real.sin (t / 2) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith [ht.2])
          (by linarith)
      linarith
    have hb : |g t| ≤ 1 / t + 1 / (2 * Real.sin (t / 2)) := by
      rw [g]
      refine (abs_sub _ _).trans (le_of_eq ?_)
      rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
    have h1 : 1 / t ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h2 : 1 / (2 * Real.sin (t / 2)) ≤ π / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 2 ≤ π * Real.sin (t / 2) := by
        rw [div_le_iff₀ Real.pi_pos] at hsin1
        linarith
      linarith
    linarith [Real.pi_le_four]

/-- On `(0, π]`: `sin((n+½)t)/t = D_n(t) + sin((n+½)t) g(t)`. -/
theorem sin_div_eq (n : ℕ) (t : ℝ) (h0 : 0 < t) (hπ : t ≤ π) :
    Real.sin ((n + 1 / 2) * t) / t = D n t + Real.sin ((n + 1 / 2) * t) * g t := by
  have hs : 0 < Real.sin (t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hD : D n t = Real.sin ((n + 1 / 2) * t) / (2 * Real.sin (t / 2)) := by
    rw [eq_div_iff (by positivity), D, ← dirichlet_kernel]
    ring
  rw [hD, g]
  field_simp
  ring

/-! ### Riemann–Lebesgue -/

/-- `∫₀^π g(t) sin(λ t) dt → 0` as `λ → ∞`. -/
theorem tendsto_integral_g_sin :
    Tendsto (fun lam : ℝ => ∫ t in (0 : ℝ)..π, g t * Real.sin (lam * t)) atTop (𝓝 0) := by
  set F : ℝ → ℂ := (Set.Icc 0 π).indicator (fun t => (g t : ℂ)) with hF
  have hRL := Real.tendsto_integral_exp_smul_cocompact F
  have hw : Tendsto (fun lam : ℝ => lam / (2 * π)) atTop (cocompact ℝ) := by
    rw [cocompact_eq_atBot_atTop]
    exact (tendsto_id.atTop_div_const (by positivity)).mono_right le_sup_right
  have h2 := (Complex.continuous_im.tendsto 0).comp (hRL.comp hw)
  simp only [Complex.zero_im, Function.comp_def] at h2
  -- identify the imaginary part
  have key : ∀ lam : ℝ, (∫ v : ℝ, 𝐞 (-(v * (lam / (2 * π)))) • F v).im =
      -∫ t in (0 : ℝ)..π, g t * Real.sin (lam * t) := by
    intro lam
    set E : ℝ → ℂ := fun v =>
      Complex.exp (((2 * π * -(v * (lam / (2 * π))) : ℝ) : ℂ) * Complex.I) with hE
    have hpt : ∀ v, 𝐞 (-(v * (lam / (2 * π)))) • F v =
        (Set.Icc 0 π).indicator (fun v => E v * (g v : ℂ)) v := by
      intro v
      rw [hF]
      by_cases hv : v ∈ Set.Icc 0 π
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, Circle.smul_def, smul_eq_mul,
          Real.fourierChar_apply]
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, smul_zero]
    simp_rw [hpt]
    rw [MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc]
    have hmeas : Measurable E := by
      rw [hE]
      exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp (by fun_prop)).mul_const _)
    have hnormE : ∀ v, ‖E v‖ = 1 := fun v => by rw [hE]; exact Complex.norm_exp_ofReal_mul_I _
    have hint : IntegrableOn (fun v => E v * (g v : ℂ)) (Set.Ioc 0 π) := by
      refine Measure.integrableOn_of_bounded (M := 2) (by simp) ?_ ?_
      · exact (hmeas.mul (Complex.measurable_ofReal.comp measurable_g)).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun v hv => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormE, one_mul]
        exact abs_g_le v ⟨hv.1.le, hv.2⟩
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, ← MeasureTheory.integral_neg]
    have him := integral_im hint
    change (∫ t in Set.Ioc 0 π, E t * (g t : ℂ)).im = _
    rw [show (∫ t in Set.Ioc 0 π, E t * (g t : ℂ)).im =
        RCLike.im (∫ t in Set.Ioc 0 π, E t * (g t : ℂ)) from rfl, ← him]
    refine setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_
    change (E v * (g v : ℂ)).im = _
    simp only [hE]
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      Complex.exp_ofReal_mul_I_im]
    have : 2 * π * -(v * (lam / (2 * π))) = -(lam * v) := by field_simp
    rw [this, Real.sin_neg]
    ring
  simp_rw [key] at h2
  simpa using h2.neg

/-! ### The Dirichlet integral -/

theorem Si_half_eq (n : ℕ) :
    Si ((n + 1 / 2) * π) = ∫ t in (0 : ℝ)..π, Real.sin ((n + 1 / 2) * t) / t := by
  have hc : ((n : ℝ) + 1 / 2) ≠ 0 := by positivity
  unfold Si
  have h1 := intervalIntegral.integral_comp_mul_left (a := 0) (b := π) (f := sinc) hc
  rw [mul_zero] at h1
  have h2 : ∫ t in (0 : ℝ)..π, Real.sin ((n + 1 / 2) * t) / t =
      ∫ t in (0 : ℝ)..π, ((n : ℝ) + 1 / 2) * sinc (((n : ℝ) + 1 / 2) * t) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [sinc]
    rcases eq_or_ne t 0 with h | h
    · simp [h]
    · field_simp
  rw [h2, intervalIntegral.integral_const_mul, h1, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc,
    one_mul]

theorem intervalIntegrable_g_sin (c : ℝ) :
    IntervalIntegrable (fun t => g t * Real.sin (c * t)) volume 0 π := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le]
  refine Measure.integrableOn_of_bounded (M := 2) (by simp) ?_ ?_
  · exact (measurable_g.mul (by fun_prop)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun v hv => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |g v| * |Real.sin (c * v)| ≤ 2 * 1 :=
          mul_le_mul (abs_g_le v ⟨hv.1.le, hv.2⟩) (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num

theorem Si_half_eq' (n : ℕ) :
    Si ((n + 1 / 2) * π) = π / 2 + ∫ t in (0 : ℝ)..π, g t * Real.sin ((n + 1 / 2) * t) := by
  rw [Si_half_eq, ← integral_D n, ← intervalIntegral.integral_add
    ((continuous_D n).intervalIntegrable _ _) (intervalIntegrable_g_sin _)]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
  rw [Set.uIoc_of_le Real.pi_pos.le] at ht
  rw [sin_div_eq n t ht.1 ht.2]
  ring

theorem tendsto_Si_half :
    Tendsto (fun n : ℕ => Si ((n + 1 / 2) * π)) atTop (𝓝 (π / 2)) := by
  simp_rw [Si_half_eq']
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1 / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have := tendsto_integral_g_sin.comp hn
  simpa [Function.comp_def] using tendsto_const_nhds.add this

/-- **The Dirichlet integral**: `Si y → π/2`. -/
theorem tendsto_Si : Tendsto Si atTop (𝓝 (π / 2)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n₁, hn₁⟩ := Metric.tendsto_atTop.1 tendsto_Si_half (ε / 2) (by linarith)
  obtain ⟨n₂, hn₂⟩ : ∃ n₂ : ℕ, 4 / (ε * π) < n₂ := exists_nat_gt _
  set n := max n₁ n₂ with hn
  have hpos : 0 < ((n : ℝ) + 1 / 2) * π := by positivity
  refine ⟨((n : ℝ) + 1 / 2) * π, fun y hy => ?_⟩
  have h1 := hn₁ n (le_max_left _ _)
  rw [Real.dist_eq] at h1 ⊢
  have h2 := abs_Si_sub_le _ y hpos hy
  have h3 : 2 / (((n : ℝ) + 1 / 2) * π) < ε / 2 := by
    have hn2 : (n₂ : ℝ) ≤ n := by exact_mod_cast le_max_right n₁ n₂
    have h4 : 4 / (ε * π) < (n : ℝ) := lt_of_lt_of_le hn₂ hn2
    rw [div_lt_iff₀ (by positivity)] at h4
    rw [div_lt_iff₀ hpos]
    nlinarith [Real.pi_pos]
  calc |Si y - π / 2| ≤ |Si y - Si (((n : ℝ) + 1 / 2) * π)| + |Si (((n : ℝ) + 1 / 2) * π) - π / 2| :=
        abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (h2.trans h3.le) h1
    _ = ε := by ring

/-- `|Si y - π/2| ≤ 2 / y` for `y > 0`. -/
theorem abs_Si_sub_pi_div_two_le (y : ℝ) (hy : 0 < y) : |Si y - π / 2| ≤ 2 / y := by
  have h := le_of_tendsto (f := fun y' => |Si y' - Si y|) ((tendsto_Si.sub_const (Si y)).abs)
    (Filter.eventually_atTop.2 ⟨y, fun y' h' => abs_Si_sub_le y y' hy h'⟩)
  rwa [abs_sub_comm] at h


end SineIntegral

end LeanProofs.IntegerPoints
