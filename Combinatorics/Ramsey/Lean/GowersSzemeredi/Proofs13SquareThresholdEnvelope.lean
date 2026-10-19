import GowersSzemeredi.Proofs13ThresholdExponentialEnvelope
import GowersSzemeredi.Proofs13SquareScale

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
  have key {C D e : Real} (hD : 0 < D) (he : 0 ≤ e) (hC : C ≤ Real.exp A)
      (hDi : D⁻¹ ≤ Real.exp A) (hEi : e⁻¹ ≤ Real.exp (2 * A)) :
      positivePowerThreshold C D e ≤ Real.exp (Real.exp (4 * A)) :=
    (positivePowerThreshold_le_double_exp hD he hA0 zero_le_one zero_le_one
      (by rwa [one_mul]) (by rwa [one_mul]) hEi).trans_eq (by norm_num)
  have hf2 : f⁻¹ ≤ Real.exp (2 * A) := hfI.trans (Real.exp_le_exp.mpr (by linarith only [hA]))
  have h1 : (1 : Real)⁻¹ ≤ Real.exp A := inv_one.trans_le (Real.one_le_exp_iff.mpr hA0)
  refine max_le (key one_pos hf.le h8 h1 hf2) (max_le (key one_pos hf.le hW h1 hf2)
    (key (by positivity) (mul_pos hf hg).le h8 ?_ ?_))
  · rw [one_div, Real.inv_rpow (by norm_num : (0 : Real) ≤ 4), inv_inv]
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hg1).trans
      (by rw [Real.rpow_one]; linarith)
  · rw [mul_inv, two_mul, Real.exp_add]
    gcongr

/-- The outer length threshold adds only two units to the inner exponential
budget. This accounts for the small initial length coefficient c. -/
theorem squareScaleThreshold_le_double_exp {c e f g W A : Real}
    (hc : 0 < c) (he : 0 < e) (hf : 0 < f) (hg : 0 < g) (hg1 : g ≤ 1) (hA : 4 ≤ A)
    (hcI : c⁻¹ ≤ Real.exp A) (heI : e⁻¹ ≤ Real.exp A)
    (hfI : f⁻¹ ≤ Real.exp A) (hgI : g⁻¹ ≤ Real.exp A) (hW : W ≤ Real.exp A) :
    squareScaleThreshold c e f g W ≤ Real.exp (Real.exp (6 * A)) := by
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
  have hpow {x y B : Real} (hx : 0 < x) (hy : 0 ≤ y) (hy1 : y ≤ 1) (hB : 0 ≤ B)
      (h : x⁻¹ ≤ Real.exp B) : (x ^ y)⁻¹ ≤ Real.exp B := by
    rw [← Real.inv_rpow hx.le]
    exact (Real.rpow_le_rpow (inv_nonneg.2 hx.le) h hy).trans
      ((Real.exp_mul B y).symm.trans_le (Real.exp_le_exp.mpr (mul_le_of_le_one_right hB hy1)))
  have hcf := hpow hc hf.le hf1 hA0 hcI
  have hef : (e * f)⁻¹ ≤ Real.exp (2 * A) := by
    rw [mul_inv, two_mul, Real.exp_add]
    gcongr
  have hcoef := hpow (by positivity : 0 < c ^ f / 4) (by positivity : 0 ≤ g / 2)
    (by linarith) (by positivity : 0 ≤ 2 * A)
    (by rw [inv_div, div_eq_mul_inv, two_mul, Real.exp_add]; gcongr; linarith)
  have hefg : (e * f * g / 4)⁻¹ ≤ Real.exp (4 * A) := by
    rw [inv_div, div_eq_mul_inv, mul_inv, show 4 * A = A + (2 * A + A) by ring,
      Real.exp_add, Real.exp_add]
    gcongr
    linarith
  refine max_le ((positivePowerThreshold_le_double_exp (C := 4) (Real.rpow_pos_of_pos hc f)
      (mul_pos he hf).le hA0 zero_le_one zero_le_one (by rw [one_mul]; linarith)
      (by rwa [one_mul]) hef).trans ?_) ((positivePowerThreshold_le_double_exp (C := 2)
      (by positivity) (by positivity) hA0 zero_le_one zero_le_two (by rw [one_mul]; linarith)
      hcoef hefg).trans_eq (by norm_num))
  exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith))

end LeanProofs.GowersSzemeredi
