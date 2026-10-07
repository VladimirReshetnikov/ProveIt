import GowersSzemeredi.Proofs13ExplicitSquareScale
import GowersSzemeredi.Proofs13ThresholdExponentialEnvelope

/-! Double-exponential bounds for the final square-extraction thresholds,
with explicit budgets for every reciprocal coefficient and exponent. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem eight_le_exp_of_four_le {A : Real} (hA : 4 ≤ A) : 8 ≤ Real.exp A := by
  have htwo : (2 : Real) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : Real)
    linarith only [h]
  have hcube := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) htwo 3
  have hthree : (8 : Real) ≤ Real.exp 3 := by
    norm_num [← Real.exp_nat_mul] at hcube
    exact hcube
  exact hthree.trans (Real.exp_le_exp.mpr (by linarith only [hA]))

/-- The first square scales have a double-exponential bound when all
reciprocal exponents and the required width have exponential budgets. -/
theorem squareLengthThreshold_le_double_exp {f g W A : Real}
    (hf : 0 < f) (hg : 0 < g) (hg1 : g ≤ 1) (hA : 4 ≤ A)
    (hfI : f⁻¹ ≤ Real.exp A) (hgI : g⁻¹ ≤ Real.exp A) (hW : W ≤ Real.exp A) :
    squareLengthThreshold f g W ≤ Real.exp (Real.exp (4 * A)) := by
  have hA0 : 0 ≤ A := by linarith only [hA]
  have h8 := eight_le_exp_of_four_le hA
  have hf2 : f⁻¹ ≤ Real.exp (2 * A) := hfI.trans (Real.exp_le_exp.mpr (by linarith only [hA]))
  have hfg : (f * g)⁻¹ ≤ Real.exp (2 * A) := by
    rw [mul_inv_rev, show 2 * A = A + A by ring, Real.exp_add]
    exact mul_le_mul hgI hfI (by positivity) (Real.exp_pos _).le
  have hD : ((1 / 4 : Real) ^ g)⁻¹ ≤ Real.exp A := by
    rw [← Real.inv_rpow (by norm_num : (0 : Real) ≤ 1 / 4)]
    norm_num only [one_div, inv_inv]
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 4) hg1).trans
      (by simpa only [Real.rpow_one] using (show (4 : Real) ≤ Real.exp A by linarith only [h8]))
  have h1 : (1 : Real)⁻¹ ≤ Real.exp A := by
    simpa using Real.one_le_exp_iff.mpr hA0
  have hleft := positivePowerThreshold_le_double_exp (C := 8) zero_lt_one hf.le hA0
    (by norm_num : (0 : Real) ≤ 1) (by norm_num : (0 : Real) ≤ 1)
    (by simpa only [one_mul] using h8) (by simpa only [one_mul] using h1) hf2
  have hmid := positivePowerThreshold_le_double_exp (C := W) zero_lt_one hf.le hA0
    (by norm_num : (0 : Real) ≤ 1) (by norm_num : (0 : Real) ≤ 1)
    (by simpa only [one_mul] using hW) (by simpa only [one_mul] using h1) hf2
  have hright := positivePowerThreshold_le_double_exp
    (Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 1 / 4) g) (mul_pos hf hg).le hA0
    (by norm_num : (0 : Real) ≤ 1) (by norm_num : (0 : Real) ≤ 1)
    (by simpa only [one_mul] using h8) (by simpa only [one_mul] using hD) hfg
  exact max_le (by norm_num at hleft; exact hleft) (max_le (by norm_num at hmid; exact hmid) (by norm_num at hright; exact hright))

/-- The outer length threshold adds only two units to the inner exponential
budget. This accounts for the small initial length coefficient c. -/
theorem squareScaleThreshold_le_double_exp {c e f g W A : Real}
    (hc : 0 < c) (he : 0 < e) (hf : 0 < f) (hg : 0 < g) (hg1 : g ≤ 1) (hA : 4 ≤ A)
    (hcI : c⁻¹ ≤ Real.exp A) (heI : e⁻¹ ≤ Real.exp A)
    (hfI : f⁻¹ ≤ Real.exp A) (hgI : g⁻¹ ≤ Real.exp A) (hW : W ≤ Real.exp A) :
    squareScaleThreshold c e f g W ≤ Real.exp (Real.exp (6 * A)) := by
  have hA0 : 0 ≤ A := by linarith only [hA]
  have hlength := squareLengthThreshold_le_double_exp hf hg hg1 hA hfI hgI hW
  have h := positivePowerThreshold_le_exp hc he.le
    (show 0 ≤ Real.exp (4 * A) + A by positivity) hlength hcI heI
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hlin : A ≤ Real.exp (4 * A) := by
    have hh := Real.add_one_le_exp (4 * A)
    linarith only [hh, hA]
  have htwo : (2 : Real) ≤ Real.exp A := (by norm_num : (2 : Real) ≤ 8).trans (eight_le_exp_of_four_le hA)
  calc
    _ ≤ (2 * Real.exp (4 * A)) * Real.exp A :=
      mul_le_mul_of_nonneg_right (by linarith only [hlin]) (Real.exp_pos _).le
    _ ≤ (Real.exp A * Real.exp (4 * A)) * Real.exp A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- Rounded square lengths and the final subtraction of one also have a
double-exponential threshold. Both small coefficients are accounted for. -/
theorem squarePowerThreshold_le_double_exp {c e f g A : Real}
    (hc : 0 < c) (he : 0 < e) (hf : 0 < f) (hf1 : f ≤ 1)
    (hg : 0 < g) (hg1 : g ≤ 1) (hA : 4 ≤ A)
    (hcI : c⁻¹ ≤ Real.exp A) (heI : e⁻¹ ≤ Real.exp A)
    (hfI : f⁻¹ ≤ Real.exp A) (hgI : g⁻¹ ≤ Real.exp A) :
    squarePowerThreshold c e f g ≤ Real.exp (Real.exp (7 * A)) := by
  have hA0 : 0 ≤ A := by linarith only [hA]
  have h8 := eight_le_exp_of_four_le hA
  have hcf : (c ^ f)⁻¹ ≤ Real.exp A := by
    rw [← Real.inv_rpow hc.le]
    calc
      _ ≤ (Real.exp A) ^ f := Real.rpow_le_rpow (inv_nonneg.mpr hc.le) hcI hf.le
      _ = Real.exp (A * f) := (Real.exp_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hA0, hf1])
  have hef : (e * f)⁻¹ ≤ Real.exp (2 * A) := by
    rw [mul_inv_rev, show 2 * A = A + A by ring, Real.exp_add]
    exact mul_le_mul hfI heI (by positivity) (Real.exp_pos _).le
  have hcoef : ((c ^ f / 4) ^ (g / 2))⁻¹ ≤ Real.exp (2 * A) := by
    have hinner : (c ^ f / 4)⁻¹ ≤ Real.exp (2 * A) := by
      rw [inv_div, div_eq_mul_inv, show 2 * A = A + A by ring, Real.exp_add]
      exact mul_le_mul (show (4 : Real) ≤ Real.exp A by linarith only [h8]) hcf (by positivity) (Real.exp_pos _).le
    rw [← Real.inv_rpow (by positivity : 0 ≤ c ^ f / 4)]
    calc
      _ ≤ (Real.exp (2 * A)) ^ (g / 2) := Real.rpow_le_rpow (by positivity) hinner (by positivity)
      _ = Real.exp (2 * A * (g / 2)) := (Real.exp_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hA0, hg1])
  have hefg : (e * f * g / 4)⁻¹ ≤ Real.exp (4 * A) := by
    rw [inv_div, div_eq_mul_inv, mul_inv_rev]
    calc
      _ ≤ Real.exp A * (Real.exp A * Real.exp (2 * A)) :=
        mul_le_mul (show (4 : Real) ≤ Real.exp A by linarith only [h8])
          (mul_le_mul hgI hef (by positivity) (Real.exp_pos _).le) (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hleft := positivePowerThreshold_le_double_exp (C := 4) (Real.rpow_pos_of_pos hc f)
    (mul_pos he hf).le hA0 (by norm_num : (0 : Real) ≤ 1) (by norm_num : (0 : Real) ≤ 1)
    (by simpa only [one_mul] using (show (4 : Real) ≤ Real.exp A by linarith only [h8]))
    (by simpa only [one_mul] using hcf) hef
  have hright := positivePowerThreshold_le_double_exp (C := 2)
    (Real.rpow_pos_of_pos (by positivity : 0 < c ^ f / 4) (g / 2)) (by positivity : 0 ≤ e * f * g / 4)
    hA0 (by norm_num : (0 : Real) ≤ 1) (by norm_num : (0 : Real) ≤ 2)
    (by simpa only [one_mul] using (show (2 : Real) ≤ Real.exp A by linarith only [h8])) hcoef hefg
  apply max_le
  · apply (show positivePowerThreshold 4 (c ^ f) (e * f) ≤ Real.exp (Real.exp (4 * A)) by norm_num at hleft; exact hleft).trans
    exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith only [hA0]))
  · norm_num at hright
    exact hright

end LeanProofs.GowersSzemeredi
