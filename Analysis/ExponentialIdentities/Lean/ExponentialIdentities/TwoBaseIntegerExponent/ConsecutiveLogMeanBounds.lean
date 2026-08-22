import ExponentialIdentities.TwoBaseIntegerExponent.Localization
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set

namespace LeanProofs.TwoBaseIntegerExponent

noncomputable section

/-- Reciprocal logarithmic increment, i.e. the logarithmic mean of `H` and `H+1`. -/
def consecutiveLogMean (H : ℝ) : ℝ := 1 / Real.log (1 + 1 / H)

/-- The two-term rational center for the consecutive logarithmic mean. -/
def consecutiveLogMeanCenter (H : ℝ) : ℝ := H + 1 / 2 - 1 / (12 * H)

private theorem first_log_rational_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Real.log (1 + x) < 12 * x / (12 + 6 * x - x ^ 2) := by
  let f : ℝ → ℝ := fun y ↦ 12 * y / (12 + 6 * y - y ^ 2) - Real.log (1 + y)
  have hden (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) : 0 < 12 + 6 * y - y ^ 2 := by
    have hsq : y ^ 2 ≤ y := by nlinarith [mul_nonneg hy.1 (sub_nonneg.mpr hy.2)]
    nlinarith
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    dsimp [f]
    apply ContinuousOn.sub
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro y hy
      exact (hden y hy).ne'
    · apply ContinuousOn.log
      · fun_prop
      intro y hy
      nlinarith [hy.1]
  have hderiv (y : ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
      deriv f y = y ^ 3 * (24 - y) /
        ((1 + y) * (12 + 6 * y - y ^ 2) ^ 2) := by
    have hycc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
    have hy1 : 1 + y ≠ 0 := ne_of_gt (by linarith [hy.1])
    have hd : 12 + 6 * y - y ^ 2 ≠ 0 := (hden y hycc).ne'
    have hN : HasDerivAt (fun z : ℝ ↦ 12 * z) 12 y := by
      simpa using (hasDerivAt_id y).const_mul 12
    have hD : HasDerivAt (fun z : ℝ ↦ 12 + 6 * z - z ^ 2) (6 - 2 * y) y := by
      have h := ((hasDerivAt_const y (12 : ℝ)).add
        ((hasDerivAt_id y).const_mul 6)).sub ((hasDerivAt_id y).pow 2)
      have hfun : HasDerivAt (fun z : ℝ ↦ 12 + 6 * z - z ^ 2)
          (0 + 6 * 1 - (2 : ℝ) * y ^ (2 - 1) * 1) y :=
        h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by simp [id_eq])
      convert hfun using 1
      ring
    have hL : HasDerivAt (fun z : ℝ ↦ Real.log (1 + z)) (1 + y)⁻¹ y := by
      convert (Real.hasDerivAt_log hy1).comp_const_add 1 y using 1
    have hf := (hN.div hD hd).sub hL
    change deriv (((fun z : ℝ ↦ 12 * z) / fun z : ℝ ↦ 12 + 6 * z - z ^ 2) -
      fun z : ℝ ↦ Real.log (1 + z)) y = _
    rw [hf.deriv]
    field_simp [hy1, hd]
    ring
  have hmono : StrictMonoOn f (Set.Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1) hcont
    rw [interior_Icc]
    intro y hy
    rw [hderiv y hy]
    have hycc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
    exact div_pos
      (mul_pos (pow_pos hy.1 3) (by linarith [hy.2]))
      (mul_pos (by linarith [hy.1]) (sq_pos_of_pos (hden y hycc)))
  have hfx : f 0 < f x := hmono (by simp) ⟨hx0.le, hx1⟩ hx0
  simpa [f] using hfx

private theorem second_log_rational_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    24 * x / (24 + 12 * x - 2 * x ^ 2 + x ^ 3) < Real.log (1 + x) := by
  let f : ℝ → ℝ := fun y ↦
    Real.log (1 + y) - 24 * y / (24 + 12 * y - 2 * y ^ 2 + y ^ 3)
  have hden (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
      0 < 24 + 12 * y - 2 * y ^ 2 + y ^ 3 := by
    have hsq : y ^ 2 ≤ 1 := by nlinarith [mul_nonneg hy.1 (sub_nonneg.mpr hy.2)]
    have hcub : 0 ≤ y ^ 3 := pow_nonneg hy.1 _
    nlinarith
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    dsimp [f]
    apply ContinuousOn.sub
    · apply ContinuousOn.log
      · fun_prop
      intro y hy
      nlinarith [hy.1]
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro y hy
      exact (hden y hy).ne'
  have hderiv (y : ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
      deriv f y = y ^ 4 * (y ^ 2 - 4 * y + 76) /
        ((1 + y) * (24 + 12 * y - 2 * y ^ 2 + y ^ 3) ^ 2) := by
    have hycc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
    have hy1 : 1 + y ≠ 0 := ne_of_gt (by linarith [hy.1])
    have hd : 24 + 12 * y - 2 * y ^ 2 + y ^ 3 ≠ 0 := (hden y hycc).ne'
    have hN : HasDerivAt (fun z : ℝ ↦ 24 * z) 24 y := by
      simpa using (hasDerivAt_id y).const_mul 24
    have hD : HasDerivAt (fun z : ℝ ↦ 24 + 12 * z - 2 * z ^ 2 + z ^ 3)
        (12 - 4 * y + 3 * y ^ 2) y := by
      have h := (((hasDerivAt_const y (24 : ℝ)).add
        ((hasDerivAt_id y).const_mul 12)).sub
        (((hasDerivAt_id y).pow 2).const_mul 2)).add ((hasDerivAt_id y).pow 3)
      have hfun : HasDerivAt (fun z : ℝ ↦ 24 + 12 * z - 2 * z ^ 2 + z ^ 3)
          (0 + 12 * 1 - 2 * ((2 : ℝ) * y ^ (2 - 1) * 1) +
            (3 : ℝ) * y ^ (3 - 1) * 1) y :=
        h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by simp [id_eq])
      convert hfun using 1
      ring
    have hL : HasDerivAt (fun z : ℝ ↦ Real.log (1 + z)) (1 + y)⁻¹ y := by
      convert (Real.hasDerivAt_log hy1).comp_const_add 1 y using 1
    have hf := hL.sub (hN.div hD hd)
    change deriv ((fun z : ℝ ↦ Real.log (1 + z)) -
      (fun z : ℝ ↦ 24 * z) / fun z : ℝ ↦ 24 + 12 * z - 2 * z ^ 2 + z ^ 3) y = _
    rw [hf.deriv]
    apply (eq_div_iff (mul_ne_zero hy1 (pow_ne_zero 2 hd))).2
    field_simp [hy1, hd]
    have hd' : 24 + y * 12 - y ^ 2 * 2 + y ^ 3 ≠ 0 := by
      intro hz
      apply hd
      calc
        24 + 12 * y - 2 * y ^ 2 + y ^ 3 = 24 + y * 12 - y ^ 2 * 2 + y ^ 3 := by ring
        _ = 0 := hz
    rw [mul_sub, mul_one, mul_div_cancel₀ _ (pow_ne_zero 2 hd')]
    ring
  have hmono : StrictMonoOn f (Set.Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1) hcont
    rw [interior_Icc]
    intro y hy
    rw [hderiv y hy]
    have hycc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
    have hquad : 0 < y ^ 2 - 4 * y + 76 := by nlinarith [sq_nonneg y]
    exact div_pos
      (mul_pos (pow_pos hy.1 4) hquad)
      (mul_pos (by linarith [hy.1]) (sq_pos_of_pos (hden y hycc)))
  have hfx : f 0 < f x := hmono (by simp) ⟨hx0.le, hx1⟩ hx0
  simpa [f] using hfx

/-- Sharp two-term rational enclosure for the logarithmic mean of consecutive positive reals. -/
theorem consecutiveLogMean_bounds (H : ℝ) (hH : 1 ≤ H) :
    consecutiveLogMeanCenter H < consecutiveLogMean H ∧
      consecutiveLogMean H < consecutiveLogMeanCenter H + 1 / (24 * H ^ 2) := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  let x : ℝ := 1 / H
  have hx0 : 0 < x := by simp [x, hHpos]
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hHpos).2 hH
  have hlogpos : 0 < Real.log (1 + x) := Real.log_pos (by linarith)
  have hfirst := first_log_rational_bound hx0 hx1
  have hsecond := second_log_rational_bound hx0 hx1
  have hD1 : 0 < 12 + 6 * x - x ^ 2 := by
    have hsq : x ^ 2 ≤ x := by nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hx1)]
    nlinarith
  have hD2 : 0 < 24 + 12 * x - 2 * x ^ 2 + x ^ 3 := by
    have hsq : x ^ 2 ≤ 1 := by nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hx1)]
    have hcub : 0 ≤ x ^ 3 := by positivity
    nlinarith
  have hcenter : consecutiveLogMeanCenter H = (12 + 6 * x - x ^ 2) / (12 * x) := by
    rw [consecutiveLogMeanCenter]
    dsimp [x]
    field_simp
    ring
  have hupperCenter :
      consecutiveLogMeanCenter H + 1 / (24 * H ^ 2) =
        (24 + 12 * x - 2 * x ^ 2 + x ^ 3) / (24 * x) := by
    rw [consecutiveLogMeanCenter]
    dsimp [x]
    field_simp
    ring
  change consecutiveLogMeanCenter H < 1 / Real.log (1 + x) ∧
    1 / Real.log (1 + x) < consecutiveLogMeanCenter H + 1 / (24 * H ^ 2)
  rw [hupperCenter, hcenter]
  constructor
  · apply (lt_div_iff₀ hlogpos).2
    have hratpos : 0 < 12 * x / (12 + 6 * x - x ^ 2) := div_pos (by positivity) hD1
    have hprod :
        ((12 + 6 * x - x ^ 2) / (12 * x)) *
          (12 * x / (12 + 6 * x - x ^ 2)) = 1 := by
      field_simp [ne_of_gt hx0, ne_of_gt hD1]
    calc
      (12 + 6 * x - x ^ 2) / (12 * x) * Real.log (1 + x) <
          (12 + 6 * x - x ^ 2) / (12 * x) *
            (12 * x / (12 + 6 * x - x ^ 2)) := by
        gcongr
      _ = 1 := hprod
  · rw [div_lt_iff₀ hlogpos]
    have hprod :
        (24 * x / (24 + 12 * x - 2 * x ^ 2 + x ^ 3)) *
          ((24 + 12 * x - 2 * x ^ 2 + x ^ 3) / (24 * x)) = 1 := by
      field_simp [ne_of_gt hx0, ne_of_gt hD2]
      exact div_self (by nlinarith [hD2])
    calc
      (1 : ℝ) =
          (24 * x / (24 + 12 * x - 2 * x ^ 2 + x ^ 3)) *
            ((24 + 12 * x - 2 * x ^ 2 + x ^ 3) / (24 * x)) := hprod.symm
      _ < Real.log (1 + x) *
          ((24 + 12 * x - 2 * x ^ 2 + x ^ 3) / (24 * x)) := by
        gcongr
      _ = ((24 + 12 * x - 2 * x ^ 2 + x ^ 3) / (24 * x)) *
          Real.log (1 + x) := by ring

end

end LeanProofs.TwoBaseIntegerExponent
