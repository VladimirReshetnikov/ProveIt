import GRHArticle.SingularModuli.Separated
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The coefficient test for separation of complex conjugates

Equation `smd:eq:septest` converts two integer inequalities into separation of
the conjugate moduli, given the article's analytic cusp estimate with error 2079.
-/

namespace GRHArticle.SingularModuli

open Real

private theorem exp_four_gt : 32 < exp 4 := by
  calc
    (32 : ℝ) < (5 / 2 : ℝ) ^ 4 := by norm_num
    _ ≤ exp 1 ^ 4 := by gcongr; linarith only [exp_one_gt_d9]
    _ = exp 4 := by norm_num [← exp_nat_mul]

private theorem exp_twelve_gt : 34 * 2079 < exp 12 := by
  calc
    (34 * 2079 : ℝ) < (8 / 3 : ℝ) ^ 12 := by norm_num
    _ ≤ exp 1 ^ 12 := by gcongr; linarith only [exp_one_gt_d9]
    _ = exp 12 := by norm_num [← exp_nat_mul]

/-- If successive reduced-form coefficients pass the article's integer test,
the two cusp enclosures already certify a strict factor of sixteen. -/
theorem sixteen_mul_norm_lt_of_cusp_estimates {D a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hsize : 16 * a ^ 2 ≤ D) (hgap : 16 * a ^ 2 * b ^ 2 ≤ 9 * D * (b - a) ^ 2)
    (z w : ℂ)
    (hz : |‖z‖ - exp (π * √(D : ℝ) / a)| ≤ 2079)
    (hw : |‖w‖ - exp (π * √(D : ℝ) / b)| ≤ 2079) : 16 * ‖w‖ < ‖z‖ := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hb' := ha'.trans hab'
  have hD : (0 : ℝ) ≤ D := by positivity
  have hsize' : (16 : ℝ) * a ^ 2 ≤ D := by exact_mod_cast hsize
  have hgap' : (16 : ℝ) * a ^ 2 * b ^ 2 ≤ 9 * D * ((b : ℝ) - a) ^ 2 := by
    rw [← Nat.cast_sub hab.le]
    exact_mod_cast hgap
  have hs : 4 * (a : ℝ) ≤ √(D : ℝ) := by
    apply (sq_le_sq₀ (by positivity) (sqrt_nonneg _)).1
    rw [sq_sqrt hD]
    linarith
  have hg : 4 * (a : ℝ) * b ≤ 3 * √(D : ℝ) * (b - a) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    simp only [mul_pow, sq_sqrt hD]
    linarith
  let u := π * √(D : ℝ) / a
  let v := π * √(D : ℝ) / b
  have hu : 12 < u := by
    apply (lt_div_iff₀ ha').2
    calc
      (12 : ℝ) * a < π * (4 * a) := by nlinarith only [mul_lt_mul_of_pos_right pi_gt_three ha']
      _ ≤ π * √(D : ℝ) := mul_le_mul_of_nonneg_left hs pi_pos.le
  have hratio : 4 < u - v := by
    have he : u - v = π * √(D : ℝ) * (b - a) / (a * b) := by
      dsimp [u, v]
      field_simp
    rw [he, lt_div_iff₀ (mul_pos ha' hb')]
    have hroot := lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 4) ha') hs
    have hstrict := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right pi_gt_three hroot)
      (sub_pos.mpr hab')
    linarith
  have hU := exp_twelve_gt.trans (exp_lt_exp.mpr hu)
  have hUV := exp_four_gt.trans (exp_lt_exp.mpr hratio)
  rw [exp_sub, lt_div_iff₀ (exp_pos v)] at hUV
  have lower := (abs_le.mp hz).1
  have upper := (abs_le.mp hw).2
  change -(2079 : ℝ) ≤ ‖z‖ - exp u at lower
  change ‖w‖ - exp v ≤ 2079 at upper
  linarith

end GRHArticle.SingularModuli
