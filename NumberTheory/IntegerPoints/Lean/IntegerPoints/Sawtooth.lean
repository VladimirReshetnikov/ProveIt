import IntegerPoints.SineIntegral
import IntegerPoints.Perron
import IntegerPoints.BombieriIwaniec
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The truncated Fourier expansion of the sawtooth function

For `0 < x < 1` and `H ≥ 1`,
`ψ(x) + ∑_{h=1}^{H} sin(2πhx)/(πh) ≪ 1/(H min(x, 1 − x))`, `ψ(x) = x − 1/2`.

Proof.  `S_H(x) = ∑_{h≤H} sin(2πhx)/(πh)` has derivative
`2 ∑_{h≤H} cos(2πhx) = 2D_H(2πx) − 1`, so `S_H(x) = (1/π) ∫_0^{2πx} D_H − x`.  On
`(0, π]`, `D_H(t) = sin((H+½)t)/t − sin((H+½)t) g(t)` with the bounded smooth
`g(t) = 1/t − 1/(2 sin(t/2))`, so for `2πx ≤ π`
`∫_0^{2πx} D_H = Si((2H+1)πx) − ∫_0^{2πx} sin((H+½)s) g(s) ds = π/2 + O(1/(Hx))`
(the `Si` tail bound and an integration by parts using `|g'| ≤ π²/32`).  Hence
`S_H(x) = 1/2 − x + O(1/(Hx))`; the case `x ≥ 1/2` follows from the symmetry
`S_H(1 − x) = −S_H(x)`.
-/

open Real Finset intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace Sawtooth

open SineIntegral

/-- Interval integrability of a measurable function bounded on the interval. -/
theorem intervalIntegrable_of_bounded_on {f : ℝ → ℝ} (hf : Measurable f) {C p q : ℝ}
    (hb : ∀ x ∈ Set.uIcc p q, |f x| ≤ C) : IntervalIntegrable f volume p q := by
  refine ⟨?_, ?_⟩
  · refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne
      hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    apply hb
    rw [Set.mem_uIcc]
    exact Or.inl ⟨hx.1.le, hx.2⟩
  · refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne
      hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    apply hb
    rw [Set.mem_uIcc]
    exact Or.inr ⟨hx.1.le, hx.2⟩

/-! ### The derivative of `g` is bounded on `(0, π]` -/

theorem hasDerivAt_g {t : ℝ} (h0 : 0 < t) (hπ : t ≤ π) :
    HasDerivAt g (-(1 / t ^ 2) + Real.cos (t / 2) / (4 * Real.sin (t / 2) ^ 2)) t := by
  have hs : 0 < Real.sin (t / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h1 : HasDerivAt (fun u : ℝ => 1 / u) (-(1 / t ^ 2)) t := by
    have := hasDerivAt_inv h0.ne'
    simpa [one_div] using this
  have h2 : HasDerivAt (fun u : ℝ => 2 * Real.sin (u / 2)) (2 * (Real.cos (t / 2) * (1 / 2))) t := by
    have := ((hasDerivAt_id t).div_const 2).sin.const_mul 2
    simpa using this
  have h3 : HasDerivAt (fun u : ℝ => 1 / (2 * Real.sin (u / 2)))
      (-(2 * (Real.cos (t / 2) * (1 / 2))) / (2 * Real.sin (t / 2)) ^ 2) t := by
    have := h2.inv (mul_pos two_pos hs).ne'
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    simp only [one_div, Pi.inv_apply]
  have := h1.sub h3
  refine this.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · exact Filter.Eventually.of_forall fun u => rfl
  · field_simp
    ring

/-- `|g'(t)| ≤ π²/32` on `(0, π]`. -/
theorem abs_deriv_g_le {t : ℝ} (h0 : 0 < t) (hπ : t ≤ π) :
    |(-(1 / t ^ 2) + Real.cos (t / 2) / (4 * Real.sin (t / 2) ^ 2))| ≤ π ^ 2 / 32 := by
  set s := t / 2 with hs
  have hs0 : 0 < s := by linarith
  have hsπ : s ≤ π / 2 := by linarith
  have hsin : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0 (by linarith [Real.pi_pos])
  have hsin_ge : 2 / π * s ≤ Real.sin s := Real.mul_le_sin hs0.le hsπ
  have hsin_le : Real.sin s ≤ s := Real.sin_le hs0.le
  have hsin_cube : s - s ^ 3 / 6 ≤ Real.sin s := Real.sin_ge_sub_cube hs0.le
  have hcos_le : Real.cos s ≤ 1 := Real.cos_le_one s
  have hcos_ge : 1 - s ^ 2 / 2 ≤ Real.cos s := Real.one_sub_sq_div_two_le_cos
  have ht : t = 2 * s := by rw [hs]; ring
  -- rewrite in terms of `s`
  have e : -(1 / t ^ 2) + Real.cos (t / 2) / (4 * Real.sin (t / 2) ^ 2) =
      (s ^ 2 * Real.cos s - Real.sin s ^ 2) / (4 * s ^ 2 * Real.sin s ^ 2) := by
    rw [ht, show 2 * s / 2 = s by ring]
    field_simp
    ring
  have hden0 : (0 : ℝ) < 4 * s ^ 2 * Real.sin s ^ 2 := by positivity
  rw [e, abs_div, abs_of_pos hden0]
  rw [div_le_iff₀ hden0]
  -- numerator bounds
  have hnum_le : s ^ 2 * Real.cos s - Real.sin s ^ 2 ≤ s ^ 4 / 3 := by
    have h1 : s ^ 2 * Real.cos s ≤ s ^ 2 := by nlinarith [sq_nonneg s]
    have h2 : s ^ 2 - s ^ 4 / 3 ≤ Real.sin s ^ 2 := by
      have h3 : (s - s ^ 3 / 6) ^ 2 ≤ Real.sin s ^ 2 := by
        have hnn : 0 ≤ s - s ^ 3 / 6 := by
          have : s ^ 2 ≤ 4 := by nlinarith [Real.pi_le_four]
          nlinarith
        exact pow_le_pow_left₀ hnn hsin_cube 2
      nlinarith [sq_nonneg (s ^ 3)]
    linarith
  have hnum_ge : -(s ^ 4 / 2) ≤ s ^ 2 * Real.cos s - Real.sin s ^ 2 := by
    have h1 : s ^ 2 - s ^ 4 / 2 ≤ s ^ 2 * Real.cos s := by nlinarith [sq_nonneg s]
    have h2 : Real.sin s ^ 2 ≤ s ^ 2 := by
      have := Real.sin_sq_le_sq (x := s)
      exact this
    linarith
  have habs : |s ^ 2 * Real.cos s - Real.sin s ^ 2| ≤ s ^ 4 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  -- denominator bound
  have hden : 16 / π ^ 2 * s ^ 4 ≤ 4 * s ^ 2 * Real.sin s ^ 2 := by
    have h1 : (2 / π * s) ^ 2 ≤ Real.sin s ^ 2 := pow_le_pow_left₀ (by positivity) hsin_ge 2
    have h2 : 4 * s ^ 2 * (2 / π * s) ^ 2 ≤ 4 * s ^ 2 * Real.sin s ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 4 * s ^ 2 * (2 / π * s) ^ 2 = 16 / π ^ 2 * s ^ 4 := by
      field_simp
      ring
    linarith
  calc |s ^ 2 * Real.cos s - Real.sin s ^ 2| ≤ s ^ 4 / 2 := habs
    _ = π ^ 2 / 32 * (16 / π ^ 2 * s ^ 4) := by
        field_simp
        ring
    _ ≤ π ^ 2 / 32 * (4 * s ^ 2 * Real.sin s ^ 2) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-- The derivative of `g` as a function (on `(0, π]`). -/
noncomputable def g' (t : ℝ) : ℝ := -(1 / t ^ 2) + Real.cos (t / 2) / (4 * Real.sin (t / 2) ^ 2)

theorem continuousOn_g' {δ u : ℝ} (hδ : 0 < δ) (hu : u ≤ π) :
    ContinuousOn g' (Set.Icc δ u) := by
  unfold g'
  apply ContinuousOn.add
  · apply ContinuousOn.neg
    apply ContinuousOn.div continuousOn_const (continuous_pow 2).continuousOn
    intro t ht
    have : 0 < t := by linarith [ht.1]
    positivity
  · apply ContinuousOn.div
    · exact (Real.continuous_cos.comp (continuous_id.div_const 2)).continuousOn
    · exact (continuous_const.mul ((Real.continuous_sin.comp (continuous_id.div_const 2)).pow 2)).continuousOn
    · intro t ht
      have hs : 0 < Real.sin (t / 2) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
      positivity

theorem continuousOn_g {δ u : ℝ} (hδ : 0 < δ) (hu : u ≤ π) : ContinuousOn g (Set.Icc δ u) := by
  intro t ht
  exact (hasDerivAt_g (by linarith [ht.1]) (ht.2.trans hu)).continuousAt.continuousWithinAt

/-- `|∫_δ^u sin(N s) g(s) ds| ≤ 6/N` for `0 < δ ≤ u ≤ π`, `N ≥ 1`. -/
theorem integral_sin_mul_g_le_aux {N δ u : ℝ} (hN : 1 ≤ N) (hδ : 0 < δ) (hδu : δ ≤ u)
    (hu : u ≤ π) : |∫ s in δ..u, Real.sin (N * s) * g s| ≤ 6 / N := by
  have hN0 : 0 < N := by linarith
  have hIcc : Set.uIcc δ u = Set.Icc δ u := Set.uIcc_of_le hδu
  -- integration by parts: `u₁ = g`, `v₁ = -cos(Ns)/N`
  have hgd : ∀ s ∈ Set.uIcc δ u, HasDerivAt g (g' s) s := by
    intro s hs
    rw [hIcc] at hs
    exact hasDerivAt_g (by linarith [hs.1]) (hs.2.trans hu)
  have hvd : ∀ s ∈ Set.uIcc δ u, HasDerivAt (fun s => -Real.cos (N * s) / N) (Real.sin (N * s)) s := by
    intro s _
    have := (((hasDerivAt_id' s).const_mul N).cos).neg.div_const N
    refine this.congr_deriv ?_
    first | (field_simp; done) | (field_simp; ring)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hgd hvd
    ((continuousOn_g' hδ hu).mono (by rw [hIcc])).intervalIntegrable
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
  have hint : ∫ s in δ..u, Real.sin (N * s) * g s = ∫ s in δ..u, g s * Real.sin (N * s) := by
    apply integral_congr
    intro s _
    ring
  rw [hint, hparts]
  have hgb : ∀ s ∈ Set.Icc δ u, |g s| ≤ 2 := fun s hs =>
    abs_g_le s ⟨by linarith [hs.1], hs.2.trans hu⟩
  have hg'b : ∀ s ∈ Set.Icc δ u, |g' s| ≤ π ^ 2 / 32 := fun s hs =>
    abs_deriv_g_le (by linarith [hs.1]) (hs.2.trans hu)
  have hcos : ∀ s : ℝ, |(-Real.cos (N * s) / N)| ≤ 1 / N := by
    intro s
    rw [abs_div, abs_neg, abs_of_pos hN0]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hN0.le
  have hbd : |g u * (-Real.cos (N * u) / N) - g δ * (-Real.cos (N * δ) / N)| ≤ 4 / N := by
    calc |g u * (-Real.cos (N * u) / N) - g δ * (-Real.cos (N * δ) / N)|
        ≤ |g u| * |(-Real.cos (N * u) / N)| + |g δ| * |(-Real.cos (N * δ) / N)| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ 2 * (1 / N) + 2 * (1 / N) := by
          gcongr
          · exact hgb u ⟨hδu, le_rfl⟩
          · exact hcos u
          · exact hgb δ ⟨le_rfl, hδu⟩
          · exact hcos δ
      _ = 4 / N := by ring
  have hI : |∫ s in δ..u, g' s * (-Real.cos (N * s) / N)| ≤ π ^ 2 / 32 * π / N := by
    have := norm_integral_le_of_norm_le_const (a := δ) (b := u) (C := π ^ 2 / 32 * (1 / N))
      (f := fun s => g' s * (-Real.cos (N * s) / N)) (fun s hs => by
        rw [Set.uIoc_of_le hδu] at hs
        rw [Real.norm_eq_abs, abs_mul]
        have h1 := hg'b s ⟨hs.1.le, hs.2⟩
        have h2 := hcos s
        have h3 : 0 ≤ |g' s| := abs_nonneg _
        have h4 : 0 ≤ π ^ 2 / 32 := by positivity
        nlinarith [abs_nonneg (-Real.cos (N * s) / N)])
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    have : |u - δ| ≤ π := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    calc π ^ 2 / 32 * (1 / N) * |u - δ| ≤ π ^ 2 / 32 * (1 / N) * π :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = π ^ 2 / 32 * π / N := by ring
  have hpi : π ≤ 4 := Real.pi_le_four
  calc |g u * (-Real.cos (N * u) / N) - g δ * (-Real.cos (N * δ) / N) -
        ∫ s in δ..u, g' s * (-Real.cos (N * s) / N)|
      ≤ |g u * (-Real.cos (N * u) / N) - g δ * (-Real.cos (N * δ) / N)| +
        |∫ s in δ..u, g' s * (-Real.cos (N * s) / N)| := abs_sub _ _
    _ ≤ 4 / N + π ^ 2 / 32 * π / N := add_le_add hbd hI
    _ ≤ 6 / N := by
        rw [← add_div, div_le_div_iff_of_pos_right hN0]
        have hp2 : π ^ 2 ≤ 16 := by nlinarith [Real.pi_pos]
        have h3 : π ^ 2 / 32 * π ≤ 2 := by nlinarith [Real.pi_pos]
        linarith

/-- `|∫_0^u sin(N s) g(s) ds| ≤ 6/N` for `0 < u ≤ π`, `N ≥ 1`. -/
theorem integral_sin_mul_g_le {N u : ℝ} (hN : 1 ≤ N) (hu0 : 0 < u) (hu : u ≤ π) :
    |∫ s in (0 : ℝ)..u, Real.sin (N * s) * g s| ≤ 6 / N := by
  -- the integrand is bounded, so the integral over `[0, δ]` is `O(δ)`; let `δ → 0`
  have hN0 : 0 < N := by linarith
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) π, |Real.sin (N * s) * g s| ≤ 2 := by
    intro s hs
    rw [abs_mul]
    have := abs_g_le s hs
    have h1 := Real.abs_sin_le_one (N * s)
    nlinarith [abs_nonneg (Real.sin (N * s)), abs_nonneg (g s)]
  have hmeas : Measurable fun s => Real.sin (N * s) * g s :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).measurable.mul measurable_g
  have hint : ∀ p q : ℝ, 0 ≤ p → q ≤ π → p ≤ q →
      IntervalIntegrable (fun s => Real.sin (N * s) * g s) volume p q := by
    intro p q hp hq hpq
    apply intervalIntegrable_of_bounded_on hmeas (C := 2)
    intro s hs
    rw [Set.mem_uIcc] at hs
    apply hbound
    rcases hs with hs | hs
    · exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- for every `0 < δ ≤ u`: `|∫_0^u| ≤ 2δ + 6/N`
  have hδ : ∀ δ : ℝ, 0 < δ → δ ≤ u →
      |∫ s in (0 : ℝ)..u, Real.sin (N * s) * g s| ≤ 2 * δ + 6 / N := by
    intro δ hδ0 hδu
    rw [← integral_add_adjacent_intervals (hint 0 δ le_rfl (by linarith) hδ0.le) (hint δ u hδ0.le hu hδu)]
    have h1 : |∫ s in (0 : ℝ)..δ, Real.sin (N * s) * g s| ≤ 2 * δ := by
      have := norm_integral_le_of_norm_le_const (a := 0) (b := δ) (C := 2)
        (f := fun s => Real.sin (N * s) * g s) (fun s hs => by
          rw [Set.uIoc_of_le hδ0.le] at hs
          rw [Real.norm_eq_abs]
          exact hbound s ⟨hs.1.le, by linarith [hs.2]⟩)
      rw [Real.norm_eq_abs, sub_zero, abs_of_pos hδ0] at this
      exact this
    have h2 := integral_sin_mul_g_le_aux hN hδ0 hδu hu
    calc _ ≤ |∫ s in (0 : ℝ)..δ, Real.sin (N * s) * g s| +
          |∫ s in δ..u, Real.sin (N * s) * g s| := abs_add_le _ _
      _ ≤ 2 * δ + 6 / N := add_le_add h1 h2
  -- let `δ → 0`
  by_contra hcon
  push Not at hcon
  set ε := |∫ s in (0 : ℝ)..u, Real.sin (N * s) * g s| - 6 / N with hε
  have hε0 : 0 < ε := by linarith
  have := hδ (min (ε / 4) u) (lt_min (by linarith) hu0) (min_le_right _ _)
  have h3 : min (ε / 4) u ≤ ε / 4 := min_le_left _ _
  linarith

/-! ### The partial sums of the sawtooth series -/

/-- `S_H(x) = ∑_{h=1}^{H} sin(2πhx)/(πh)`. -/
noncomputable def S (H : ℕ) (x : ℝ) : ℝ :=
  ∑ h ∈ Finset.range H, Real.sin (2 * π * (h + 1) * x) / (π * (h + 1))

theorem S_neg (H : ℕ) (x : ℝ) : S H (-x) = -S H x := by
  unfold S
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [show 2 * π * (h + 1) * -x = -(2 * π * (h + 1) * x) by ring, Real.sin_neg, neg_div]

theorem S_add_one (H : ℕ) (x : ℝ) : S H (x + 1) = S H x := by
  unfold S
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [show 2 * π * (h + 1) * (x + 1) = 2 * π * (h + 1) * x + (h + 1 : ℕ) * (2 * π) by push_cast; ring,
    Real.sin_add_nat_mul_two_pi]

/-- `S_H'(x) = 2 D_H(2πx) − 1`. -/
theorem hasDerivAt_S (H : ℕ) (x : ℝ) :
    HasDerivAt (S H) (2 * D H (2 * π * x) - 1) x := by
  have hd : ∀ h : ℕ, HasDerivAt (fun x : ℝ => Real.sin (2 * π * (h + 1) * x) / (π * (h + 1)))
      (2 * Real.cos ((h + 1) * (2 * π * x))) x := by
    intro h
    have h0 : (π * (h + 1) : ℝ) ≠ 0 := by positivity
    have := (((hasDerivAt_id x).const_mul (2 * π * (h + 1))).sin).div_const (π * (h + 1))
    refine this.congr_deriv ?_
    simp only [id]
    rw [show (h + 1 : ℝ) * (2 * π * x) = 2 * π * (h + 1) * x by ring]
    first | (field_simp; done) | (field_simp; ring)
  have := HasDerivAt.fun_sum (u := Finset.range H)
    (A := fun h x => Real.sin (2 * π * (h + 1) * x) / (π * (h + 1)))
    (A' := fun h => 2 * Real.cos ((h + 1) * (2 * π * x))) (fun h _ => hd h)
  refine this.congr_deriv ?_
  unfold D
  rw [mul_add, Finset.mul_sum]
  ring

/-- `S_H(x) = (1/π) ∫_0^{2πx} D_H(s) ds − x`. -/
theorem S_eq_integral (H : ℕ) (x : ℝ) :
    S H x = (1 / π) * (∫ s in (0 : ℝ)..(2 * π * x), D H s) - x := by
  have hFTC : ∫ t in (0 : ℝ)..x, (2 * D H (2 * π * t) - 1) = S H x - S H 0 :=
    integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_S H t)
      (((continuous_const.mul ((continuous_D H).comp (continuous_const.mul continuous_id))).sub
        continuous_const).intervalIntegrable _ _)
  have hS0 : S H 0 = 0 := by
    unfold S
    simp
  rw [hS0, sub_zero] at hFTC
  rw [← hFTC]
  have hsub : ∫ t in (0 : ℝ)..x, (2 * D H (2 * π * t) - 1) =
      (∫ t in (0 : ℝ)..x, 2 * D H (2 * π * t)) - ∫ t in (0 : ℝ)..x, (1 : ℝ) := by
    rw [intervalIntegral.integral_sub]
    · exact (continuous_const.mul ((continuous_D H).comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
  rw [hsub, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one,
    intervalIntegral.integral_const_mul]
  congr 1
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left (fun s => D H s) hpi, mul_zero, smul_eq_mul]
  first | (field_simp; done) | (field_simp; ring)

/-- `∫_0^u D_H = Si((H+½)u) − ∫_0^u sin((H+½)s) g(s) ds` for `0 < u ≤ π`. -/
theorem integral_D_eq (H : ℕ) {u : ℝ} (hu0 : 0 < u) (hu : u ≤ π) :
    ∫ s in (0 : ℝ)..u, D H s =
      Si ((H + 1 / 2) * u) - ∫ s in (0 : ℝ)..u, Real.sin ((H + 1 / 2) * s) * g s := by
  have hN : (0 : ℝ) < H + 1 / 2 := by positivity
  have hSi : Si ((H + 1 / 2) * u) = ∫ s in (0 : ℝ)..u, Real.sin (s * (H + 1 / 2)) / s := by
    rw [mul_comm]
    exact (Perron.integral_sin_div_eq_Si (H + 1 / 2) u).symm
  have hi1 : IntervalIntegrable (fun s : ℝ => Real.sin (s * (H + 1 / 2)) / s) volume 0 u :=
    Perron.intervalIntegrable_sin_div (H + 1 / 2) 0 u
  have hi2 : IntervalIntegrable (fun s : ℝ => Real.sin ((H + 1 / 2) * s) * g s) volume 0 u := by
    apply intervalIntegrable_of_bounded_on
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).measurable.mul measurable_g)
      (C := 2)
    intro s hs
    rw [Set.uIcc_of_le hu0.le] at hs
    simp only [Function.comp, Pi.mul_apply, id]
    rw [abs_mul]
    have h1 := Real.abs_sin_le_one ((H + 1 / 2) * s)
    have h2 := abs_g_le s ⟨hs.1, hs.2.trans hu⟩
    nlinarith [abs_nonneg (Real.sin ((H + 1 / 2) * s)), abs_nonneg (g s)]
  rw [hSi, ← intervalIntegral.integral_sub hi1 hi2]
  apply intervalIntegral.integral_congr_ae
  have hnull : volume ({s : ℝ | ¬ (s ∈ Set.uIoc 0 u →
      D H s = Real.sin (s * (H + 1 / 2)) / s - Real.sin ((H + 1 / 2) * s) * g s)}) = 0 := by
    apply measure_mono_null (t := ∅)
    · intro s hs
      simp only [Set.mem_setOf_eq, Classical.not_imp] at hs
      obtain ⟨hs1, hs2⟩ := hs
      rw [Set.uIoc_of_le hu0.le] at hs1
      exfalso
      apply hs2
      have := sin_div_eq H s hs1.1 (hs1.2.trans hu)
      rw [mul_comm s]
      linarith
    · exact measure_empty
  rw [MeasureTheory.ae_iff]
  exact hnull

/-- For `0 < x ≤ 1/2` and `H ≥ 1`: `|S_H(x) − (1/2 − x)| ≤ 4/(Hx)`. -/
theorem S_approx {H : ℕ} (hH : 1 ≤ H) {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    |S H x - (1 / 2 - x)| ≤ 4 / (H * x) := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hpi : 3 < π := BI.pi_gt_three'
  set u : ℝ := 2 * π * x with hu
  have hu0 : 0 < u := by positivity
  have huπ : u ≤ π := by rw [hu]; nlinarith
  rw [S_eq_integral, integral_D_eq H hu0 huπ]
  set y : ℝ := (H + 1 / 2) * u with hy
  have hy0 : 0 < y := by positivity
  have hSi := Perron.abs_s_sub_half y hy0
  have hJ := integral_sin_mul_g_le (N := H + 1 / 2) (by linarith) hu0 huπ
  -- assemble
  have e1 : (1 / π) * (Si y - ∫ s in (0 : ℝ)..u, Real.sin ((H + 1 / 2) * s) * g s) - x -
      (1 / 2 - x) = (Si y / π - 1 / 2) -
        (1 / π) * ∫ s in (0 : ℝ)..u, Real.sin ((H + 1 / 2) * s) * g s := by
    ring
  rw [e1]
  have hyHx : 2 * π * H * x ≤ y := by
    rw [hy, hu]
    nlinarith
  have h1 : |Si y / π - 1 / 2| ≤ 1 / (π ^ 2 * H * x) := by
    refine hSi.trans ?_
    calc 2 / (π * y) ≤ 2 / (π * (2 * π * H * x)) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          exact mul_le_mul_of_nonneg_left hyHx Real.pi_pos.le
      _ = 1 / (π ^ 2 * H * x) := by
          first | (field_simp; done) | (field_simp; ring)
  have h2 : |(1 / π) * ∫ s in (0 : ℝ)..u, Real.sin ((H + 1 / 2) * s) * g s| ≤
      6 / (π * (H + 1 / 2)) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
    calc 1 / π * |∫ s in (0 : ℝ)..u, Real.sin ((H + 1 / 2) * s) * g s|
        ≤ 1 / π * (6 / (H + 1 / 2)) := mul_le_mul_of_nonneg_left hJ (by positivity)
      _ = 6 / (π * (H + 1 / 2)) := by field_simp
  have h3 : 6 / (π * (H + 1 / 2)) ≤ 3 / (π * H * x) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos Real.pi_pos hH0]
  calc |(Si y / π - 1 / 2) - (1 / π) * ∫ s in (0 : ℝ)..u, Real.sin ((H + 1 / 2) * s) * g s|
      ≤ |Si y / π - 1 / 2| + |(1 / π) * ∫ s in (0 : ℝ)..u, Real.sin ((H + 1 / 2) * s) * g s| :=
        abs_sub _ _
    _ ≤ 1 / (π ^ 2 * H * x) + 3 / (π * H * x) := add_le_add h1 (h2.trans h3)
    _ ≤ 4 / (H * x) := by
        have hHx : 0 < H * x := by positivity
        have e1 : 1 / (π ^ 2 * H * x) ≤ 1 / (H * x) := by
          apply one_div_le_one_div_of_le hHx
          have hp2 : 1 ≤ π ^ 2 := by nlinarith
          calc H * x = 1 * (H * x) := by ring
            _ ≤ π ^ 2 * (H * x) := mul_le_mul_of_nonneg_right hp2 hHx.le
            _ = π ^ 2 * H * x := by ring
        have e2 : 3 / (π * H * x) ≤ 3 / (H * x) := by
          apply div_le_div_of_nonneg_left (by norm_num) hHx
          nlinarith
        have e3 : 1 / (H * x) + 3 / (H * x) = 4 / (H * x) := by ring
        linarith

/-- **The truncated sawtooth expansion**: for `0 < x < 1` and `H ≥ 1`,
`|(x − 1/2) + S_H(x)| ≤ 4/(H min(x, 1 − x))`. -/
theorem sawtooth_expansion {H : ℕ} (hH : 1 ≤ H) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    |(x - 1 / 2) + S H x| ≤ 4 / (H * min x (1 - x)) := by
  rcases le_or_gt x (1 / 2) with hx | hx
  · rw [min_eq_left (by linarith)]
    have := S_approx hH hx0 hx
    rw [show (x - 1 / 2) + S H x = S H x - (1 / 2 - x) by ring]
    exact this
  · rw [min_eq_right (by linarith)]
    set x' := 1 - x with hx'
    have hx'0 : 0 < x' := by linarith
    have hx'h : x' ≤ 1 / 2 := by linarith
    have hS : S H x = -S H x' := by
      rw [hx', ← S_neg, show -(1 - x) = x - 1 by ring, ← S_add_one H (x - 1),
        show x - 1 + 1 = x by ring]
    have := S_approx hH hx'0 hx'h
    rw [hS, show (x - 1 / 2) + -S H x' = -(S H x' - (1 / 2 - x')) by rw [hx']; ring, abs_neg]
    exact this

end Sawtooth

end LeanProofs.IntegerPoints
