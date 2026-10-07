import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

theorem anchor_power_lower {p delta : ℝ} {m : ℕ} (hp : 0 ≤ p)
    (hm : (m : ℝ) ≤ p) (hdelta : Real.exp (-p) ≤ delta) :
    Real.exp (-(2 * p ^ 2)) ≤ delta ^ (2 * m) := by
  have hm' : ((2 * m : ℕ) : ℝ) ≤ 2 * p := by push_cast; linarith
  calc
    _ ≤ Real.exp (((2 * m : ℕ) : ℝ) * (-p)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp (-p) ^ (2 * m) := Real.exp_nat_mul _ _
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) hdelta _

theorem anchor_halved_power_lower {p delta : ℝ} {m : ℕ} (hp : 0 ≤ p)
    (hm : (m : ℝ) ≤ p) (hdelta : Real.exp (-p) ≤ delta) :
    Real.exp (-(2 * p ^ 2) - 1) ≤ delta ^ (2 * m) / 2 := by
  have hd0 : 0 ≤ delta := (Real.exp_nonneg _).trans hdelta
  rw [Real.exp_sub]
  apply div_le_div₀ (pow_nonneg hd0 _) (anchor_power_lower hp hm hdelta) (by norm_num)
  have h := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem anchor_branch_lower {p : ℝ} {m : ℕ} (hm : (m : ℝ) ≤ p) :
    Real.exp (-(4 * p)) ≤ Real.exp (-Real.log 4 * m) := by
  apply Real.exp_le_exp.mpr
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

theorem anchored_interval_budget {p delta : ℝ} {m : ℕ} (hp : 2 ≤ p)
    (hm : (m : ℝ) ≤ p) (hdelta : Real.exp (-p) ≤ delta) :
    Real.exp (-((p + 2) ^ 3)) ≤ delta ^ (2 * m) / 40 := by
  have hp0 : 0 ≤ p := by linarith
  have hd0 : 0 ≤ delta := (Real.exp_nonneg _).trans hdelta
  have h40 : (40 : ℝ) ≤ Real.exp 6 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 6
    rw [← Real.exp_nat_mul] at hpow
    norm_num at hpow
    linarith
  calc
    _ ≤ Real.exp (-(2 * p ^ 2) - 6) := by
      apply Real.exp_le_exp.mpr
      nlinarith [pow_nonneg hp0 3, sq_nonneg p]
    _ = Real.exp (-(2 * p ^ 2)) / Real.exp 6 := Real.exp_sub _ _
    _ ≤ _ := div_le_div₀ (pow_nonneg hd0 _) (anchor_power_lower hp0 hm hdelta) (by norm_num) h40

theorem anchored_density_budget {p delta sigma : ℝ} {m : ℕ} (hp : 2 ≤ p)
    (hm : (m : ℝ) ≤ p) (hdelta : Real.exp (-p) ≤ delta) (hsigma : Real.exp (-p) ≤ sigma) :
    Real.exp (-((p + 2) ^ 3)) ≤
      Real.exp (-Real.log 4 * m) * (delta ^ (2 * m) / 2) * sigma := by
  have hp0 : 0 ≤ p := by linarith
  have hd0 : 0 ≤ delta := (Real.exp_nonneg _).trans hdelta
  have hmul := mul_le_mul (anchor_branch_lower hm) (anchor_halved_power_lower hp0 hm hdelta)
    (Real.exp_nonneg _) (Real.exp_nonneg _)
  have htotal := mul_le_mul hmul hsigma (Real.exp_nonneg _)
    (mul_nonneg (Real.exp_nonneg _) (by positivity))
  apply le_trans _ htotal
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [pow_nonneg hp0 3, sq_nonneg p]

end Erdos3

end

end OAI
