import IntegerPoints.GKStatements
import IntegerPoints.BombieriIwaniec
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Graham–Kolesnik, Lemma 3.1 (the first-derivative test for integrals)

If `g/f'` is monotone on `[a, b]` and `λ|g| ≤ |f'|` there, then
`|∫_a^b g(x) e(f(x)) dx| ≤ 1/λ`.

Proof.  Integrate by parts with `u = g/f'` and `v = e(f)/(2πi)`, `v' = f' e(f)`:
`∫ g e(f) = [u v]_a^b − ∫ u' v`.  The boundary terms are at most `2·(1/λ)(1/2π)`,
and since `u` is monotone, `∫_a^b |u'| = |u(b) − u(a)| ≤ 2/λ`, so the integral
term is at most `(1/2π)(2/λ)`.  In total `2/(πλ) < 1/λ`.
-/

open Real Finset intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace GK31

/-- Every point of `(a, b)` is an accumulation point of `[a, b]`. -/
theorem accPt_Icc {a b x : ℝ} (hx : x ∈ Set.Ioo a b) : AccPt x (Filter.principal (Set.Icc a b)) := by
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  set δ : ℝ := min (ε / 2) ((b - x) / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith [hx.2])
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδb : δ ≤ (b - x) / 2 := min_le_right _ _
  refine ⟨x + δ, ⟨hball ?_, ⟨by linarith [hx.1], by linarith⟩⟩, by linarith⟩
  rw [Metric.mem_ball, Real.dist_eq]
  rw [abs_of_pos (by linarith : (0 : ℝ) < x + δ - x)]
  linarith

/-- The core estimate in the monotone case: `‖∫ g e(f)‖ ≤ 2/(πλ)`. -/
theorem core {a b lam : ℝ} {f g : ℝ → ℝ} (hab : a < b) (hlam : 0 < lam)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hmono : MonotoneOn (fun x => g x / deriv f x) (Set.Icc a b))
    (hb : ∀ x ∈ Set.Icc a b, deriv f x ≠ 0 ∧ lam * |g x| ≤ |deriv f x|) :
    ‖∫ x in a..b, (g x : ℂ) * e (f x)‖ ≤ 2 / (Real.pi * lam) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  -- regularity of `f'`, `f''`, `g'`
  have hf1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf'd : Differentiable ℝ (deriv f) := hf1.differentiable one_ne_zero
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hf'c : Continuous (deriv f) := hf1.continuous
  have hf''c : Continuous (deriv (deriv f)) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (0 + 1) (deriv f) from hf1)).2.2.continuous
  have hg'c : Continuous (deriv g) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) g from hg)).2.2.continuous
  have hgc : Continuous g := hg.continuous
  have hfc : Continuous f := hf.continuous
  -- the functions of the integration by parts
  set w : ℝ → ℝ := fun x => g x / deriv f x with hw
  set w' : ℝ → ℝ := fun x =>
    (deriv g x * deriv f x - g x * deriv (deriv f) x) / (deriv f x) ^ 2 with hw'
  set u : ℝ → ℂ := fun x => (w x : ℂ) with hu
  set u' : ℝ → ℂ := fun x => (w' x : ℂ) with hu'
  set v : ℝ → ℂ := fun x => e (f x) / (2 * Real.pi * Complex.I) with hv
  set v' : ℝ → ℂ := fun x => ((deriv f x : ℝ) : ℂ) * e (f x) with hv'
  have hIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab.le
  -- derivatives
  have hwd : ∀ x ∈ Set.Icc a b, HasDerivAt w (w' x) x := by
    intro x hx
    have h := ((hgd x).hasDerivAt).div ((hf'd x).hasDerivAt) (hb x hx).1
    exact h
  have hud : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x := by
    intro x hx
    rw [hIcc] at hx
    exact (hwd x hx).ofReal_comp
  have hed : ∀ x : ℝ, HasDerivAt (fun y => e (f y)) (2 * Real.pi * Complex.I * (deriv f x) * e (f x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => ((f y : ℝ) : ℂ)) ((deriv f x : ℝ) : ℂ) x :=
      ((hfd x).hasDerivAt).ofReal_comp
    have h2 := (h1.const_mul (2 * Real.pi * Complex.I)).cexp
    refine h2.congr_deriv ?_
    unfold e
    ring
  have hvd : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v' x) x := by
    intro x _
    have h := (hed x).div_const (2 * Real.pi * Complex.I)
    refine h.congr_deriv ?_
    rw [hv']
    field_simp
  -- integrability
  have hu'c : ContinuousOn u' (Set.uIcc a b) := by
    rw [hIcc, hu']
    apply Continuous.comp_continuousOn Complex.continuous_ofReal
    rw [hw']
    apply ContinuousOn.div
    · exact ((hg'c.mul hf'c).sub (hgc.mul hf''c)).continuousOn
    · exact (hf'c.pow 2).continuousOn
    · intro x hx
      exact pow_ne_zero 2 (hb x hx).1
  have hu'i : IntervalIntegrable u' volume a b := hu'c.intervalIntegrable
  have hv'i : IntervalIntegrable v' volume a b := by
    apply Continuous.intervalIntegrable
    rw [hv']
    exact (Complex.continuous_ofReal.comp hf'c).mul (by
      unfold e
      exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hfc)))
  -- integration by parts
  have hparts := integral_mul_deriv_eq_deriv_mul hud hvd hu'i hv'i
  have hint : ∫ x in a..b, (g x : ℂ) * e (f x) = ∫ x in a..b, u x * v' x := by
    apply integral_congr
    intro x hx
    rw [hIcc] at hx
    rw [hu, hv', hw]
    simp only
    have hne : ((deriv f x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hb x hx).1
    push_cast
    field_simp
  rw [hint, hparts]
  -- bounds for the pieces
  have hwb : ∀ x ∈ Set.Icc a b, |w x| ≤ 1 / lam := by
    intro x hx
    rw [hw]
    simp only
    rw [abs_div, div_le_div_iff₀ (abs_pos.2 (hb x hx).1) hlam]
    linarith [(hb x hx).2]
  have hvb : ∀ x, ‖v x‖ = 1 / (2 * Real.pi) := by
    intro x
    rw [hv]
    simp only
    rw [norm_div, norm_e]
    simp [Real.pi_pos.le]
  have hub : ∀ x ∈ Set.Icc a b, ‖u x‖ ≤ 1 / lam := by
    intro x hx
    rw [hu]
    simp only
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hwb x hx
  -- the integral of `u' v`: `u'` has constant sign
  have hw'nonneg : ∀ x ∈ Set.Ioo a b, 0 ≤ w' x := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
    exact (hwd x hx').hasDerivWithinAt.nonneg_of_monotoneOn (accPt_Icc hx) hmono
  have hw'int : ∫ x in a..b, w' x = w b - w a :=
    integral_eq_sub_of_hasDerivAt (fun x hx => hwd x (hIcc ▸ hx))
      (by
        have : ContinuousOn w' (Set.uIcc a b) := by
          rw [hIcc, hw']
          apply ContinuousOn.div
          · exact ((hg'c.mul hf'c).sub (hgc.mul hf''c)).continuousOn
          · exact (hf'c.pow 2).continuousOn
          · intro x hx
            exact pow_ne_zero 2 (hb x hx).1
        exact this.intervalIntegrable)
  have habs : ∫ x in a..b, |w' x| = ∫ x in a..b, w' x := by
    apply intervalIntegral.integral_congr_ae
    have hnull : volume ({x : ℝ | ¬ (x ∈ Set.uIoc a b → |w' x| = w' x)}) = 0 := by
      apply measure_mono_null (t := {b})
      · intro x hx
        simp only [Set.mem_setOf_eq, Classical.not_imp] at hx
        obtain ⟨hx1, hx2⟩ := hx
        rw [Set.uIoc_of_le hab.le] at hx1
        by_contra hxb
        have hxb' : x ∈ Set.Ioo a b := ⟨hx1.1, lt_of_le_of_ne hx1.2 hxb⟩
        exact hx2 (abs_of_nonneg (hw'nonneg x hxb'))
      · exact measure_singleton b
    rw [MeasureTheory.ae_iff]
    exact hnull
  have hu'v : ‖∫ x in a..b, u' x * v x‖ ≤ 1 / (2 * Real.pi) * (2 / lam) := by
    calc ‖∫ x in a..b, u' x * v x‖ ≤ ∫ x in a..b, ‖u' x * v x‖ :=
          norm_integral_le_integral_norm hab.le
      _ = ∫ x in a..b, |w' x| * (1 / (2 * Real.pi)) := by
          apply integral_congr
          intro x _
          show ‖u' x * v x‖ = |w' x| * (1 / (2 * Real.pi))
          rw [norm_mul, hvb, hu']
          simp only
          rw [Complex.norm_real, Real.norm_eq_abs]
      _ = (∫ x in a..b, |w' x|) * (1 / (2 * Real.pi)) := integral_mul_const _ _
      _ = (w b - w a) * (1 / (2 * Real.pi)) := by rw [habs, hw'int]
      _ ≤ 2 / lam * (1 / (2 * Real.pi)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have h1 := hwb b ⟨hab.le, le_rfl⟩
          have h2 := hwb a ⟨le_rfl, hab.le⟩
          rw [abs_le] at h1 h2
          have : 2 / lam = 1 / lam + 1 / lam := by ring
          linarith
      _ = 1 / (2 * Real.pi) * (2 / lam) := by ring
  -- assemble
  have hbd : ‖u b * v b - u a * v a‖ ≤ 1 / lam * (1 / (2 * Real.pi)) + 1 / lam * (1 / (2 * Real.pi)) := by
    calc ‖u b * v b - u a * v a‖ ≤ ‖u b * v b‖ + ‖u a * v a‖ := norm_sub_le _ _
      _ = ‖u b‖ * (1 / (2 * Real.pi)) + ‖u a‖ * (1 / (2 * Real.pi)) := by
          rw [norm_mul, norm_mul, hvb, hvb]
      _ ≤ 1 / lam * (1 / (2 * Real.pi)) + 1 / lam * (1 / (2 * Real.pi)) := by
          have h1 := hub b ⟨hab.le, le_rfl⟩
          have h2 := hub a ⟨le_rfl, hab.le⟩
          have h0 : 0 ≤ 1 / (2 * Real.pi) := by positivity
          exact add_le_add (mul_le_mul_of_nonneg_right h1 h0) (mul_le_mul_of_nonneg_right h2 h0)
  calc ‖u b * v b - u a * v a - ∫ x in a..b, u' x * v x‖
      ≤ ‖u b * v b - u a * v a‖ + ‖∫ x in a..b, u' x * v x‖ := norm_sub_le _ _
    _ ≤ 1 / lam * (1 / (2 * Real.pi)) + 1 / lam * (1 / (2 * Real.pi)) +
        1 / (2 * Real.pi) * (2 / lam) := add_le_add hbd hu'v
    _ = 2 / (Real.pi * lam) := by
        field_simp
        ring

end GK31

/-- **Graham–Kolesnik, Lemma 3.1** holds (with the absolute constant `1`). -/
theorem gk_lemma31_holds : gk_lemma31 := by
  refine ⟨1, fun a b lam f g hab hlam hf hg hmono hb => ?_⟩
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    rw [intervalIntegral.integral_same, norm_zero]
    positivity
  have hpi : 3 < Real.pi := BI.pi_gt_three'
  have key : ‖∫ x in a..b, (g x : ℂ) * e (f x)‖ ≤ 2 / (Real.pi * lam) := by
    rcases hmono with hm | ha
    · exact GK31.core h hlam hf hg hm hb
    · -- apply the monotone case to `-g`
      have hm : MonotoneOn (fun x => (-g) x / deriv f x) (Set.Icc a b) := by
        have : (fun x => (-g) x / deriv f x) = -(fun x => g x / deriv f x) := by
          funext x
          simp [neg_div]
        rw [this]
        exact ha.neg
      have hb' : ∀ x ∈ Set.Icc a b, deriv f x ≠ 0 ∧ lam * |(-g) x| ≤ |deriv f x| := by
        intro x hx
        refine ⟨(hb x hx).1, ?_⟩
        simp only [Pi.neg_apply, abs_neg]
        exact (hb x hx).2
      have := GK31.core h hlam hf (hg.neg) hm hb'
      have e1 : ∫ x in a..b, ((-g x : ℝ) : ℂ) * e (f x) = -∫ x in a..b, (g x : ℂ) * e (f x) := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro x _
        simp
      rw [e1, norm_neg] at this
      exact this
  calc ‖∫ x in a..b, (g x : ℂ) * e (f x)‖ ≤ 2 / (Real.pi * lam) := key
    _ ≤ 1 / lam := by
        rw [div_le_div_iff₀ (by positivity) hlam]
        nlinarith

end LeanProofs.IntegerPoints
