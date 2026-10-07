import OAI.Combinatorics.Progressions.Probability.PositiveDensityNormalization

namespace OAI

section

namespace Erdos3

theorem allocated_native_approximation_error
    {u p Q P K cap tau ε : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hQ : 0 ≤ Q)
    (hK : 0 ≤ K) (hcap : 0 ≤ cap)
    (hKP : K ≤ Real.exp p) (hcapP : cap ≤ Real.exp p)
    (htau : tau ≤ Real.exp (-(u + 3)))
    (hP : u + 2 * p + Q + 30 ≤ P)
    (hε : ε ≤ 6 * positiveProjectionAccuracy P) :
    2 * tau + 2 * K * (cap + 2 / Real.exp (-Q)) * ε ≤ Real.exp (-u) := by
  have hP0 : 0 ≤ P := by linarith
  have hεP : ε ≤ 2 * Real.exp (-P) := by
    have h := (positiveProjectionAccuracy_mass_bound hP0).1
    linarith
  have hcapQ : cap + 2 / Real.exp (-Q) ≤ 3 * Real.exp (p + Q) := by
    have h1 := Real.exp_le_exp.mpr (le_add_of_nonneg_right hQ : p ≤ p + Q)
    have h2 := Real.exp_le_exp.mpr (le_add_of_nonneg_left hp : Q ≤ p + Q)
    simp only [Real.exp_neg, div_eq_mul_inv, inv_inv]
    linarith
  have htail : 2 * K * (cap + 2 / Real.exp (-Q)) * ε ≤
      12 * Real.exp (2 * p + Q - P) := by
    calc
      _ ≤ 2 * K * (cap + 2 / Real.exp (-Q)) * (2 * Real.exp (-P)) :=
        mul_le_mul_of_nonneg_left hεP (by positivity)
      _ ≤ 2 * Real.exp p * (3 * Real.exp (p + Q)) * (2 * Real.exp (-P)) := by
        gcongr
      _ = 12 * (Real.exp p * Real.exp (p + Q) * Real.exp (-P)) := by ring
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
  have h3 : 2 * Real.exp (-3 : ℝ) ≤ 1 / 2 := by
    have he : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
    calc
      _ = 2 / Real.exp 3 := by rw [Real.exp_neg, div_eq_mul_inv]
      _ ≤ 2 / (4 : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) he
      _ = _ := by norm_num
  have h30 : 12 * Real.exp (-30 : ℝ) ≤ 1 / 2 := by
    have he : (24 : ℝ) ≤ Real.exp 30 := by linarith [Real.add_one_le_exp (30 : ℝ)]
    calc
      _ = 12 / Real.exp 30 := by rw [Real.exp_neg, div_eq_mul_inv]
      _ ≤ 12 / (24 : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) he
      _ = _ := by norm_num
  have hsmall : 2 * tau ≤ Real.exp (-u) / 2 := by
    calc
      _ ≤ 2 * Real.exp (-(u + 3)) := mul_le_mul_of_nonneg_left htau (by norm_num)
      _ = Real.exp (-u) * (2 * Real.exp (-3)) := by rw [neg_add, Real.exp_add]; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h3 (Real.exp_nonneg (-u))]
  have htail' : 2 * K * (cap + 2 / Real.exp (-Q)) * ε ≤ Real.exp (-u) / 2 := by
    apply htail.trans
    calc
      _ ≤ 12 * Real.exp (-u - 30) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
      _ = Real.exp (-u) * (12 * Real.exp (-30)) := by rw [sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h30 (Real.exp_nonneg (-u))]
  linarith

end Erdos3

end

end OAI
