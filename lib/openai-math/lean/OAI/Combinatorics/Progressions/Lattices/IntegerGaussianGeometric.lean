import Mathlib

namespace OAI

section

namespace Erdos3

theorem hasSum_geometric_natAbs {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℤ => r ^ n.natAbs) ((1 - r)⁻¹ + r * (1 - r)⁻¹) := by
  have h := hasSum_geometric_of_lt_one hr hr1
  apply HasSum.of_nat_of_neg_add_one
  · simpa using h
  · convert! h.mul_left r using 1
    funext n
    have hn : (-((n : ℤ) + 1)).natAbs = n + 1 := by
      rw [Int.natAbs_neg, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega]
      rfl
    rw [hn, pow_succ, mul_comm]

theorem integer_geometric_sum_bound {t : ℝ} (ht : 0 < t) :
    (∑' n : ℤ, (Real.exp (-1 / t)) ^ n.natAbs) ≤ 1 + 2 * t := by
  let r := Real.exp (-1 / t)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) ht)
  rw [(hasSum_geometric_natAbs hr.le hr1).tsum_eq]
  have hs : 0 < 1 - r := by linarith
  have he : r * Real.exp (1 / t) = 1 := by
    dsimp [r]
    rw [← Real.exp_add, show -1 / t + 1 / t = 0 by ring, Real.exp_zero]
  have hlin : t * r + r ≤ t := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1 / t)) (mul_pos ht hr).le
    have hl : t * r * (1 / t + 1) = t * r + r := by field_simp; ring
    have hu : t * r * Real.exp (1 / t) = t := by rw [mul_assoc, he, mul_one]
    rwa [hl, hu] at h
  have hid : (1 - r)⁻¹ + r * (1 - r)⁻¹ = (1 + r) / (1 - r) := by ring
  rw [hid]
  apply (div_le_iff₀ hs).mpr
  nlinarith

theorem integer_gaussian_le_geometric (n : ℤ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-Real.pi / t * (n : ℝ) ^ 2) ≤ (Real.exp (-1 / t)) ^ n.natAbs := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hn : (n.natAbs : ℝ) ≤ (n.natAbs : ℝ) ^ 2 := by
    exact_mod_cast (show n.natAbs ≤ n.natAbs ^ 2 by simpa only [pow_two] using Nat.le_mul_self n.natAbs)
  have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by simp
  rw [habs, sq_abs] at hn
  have hpi : |(n : ℝ)| ≤ Real.pi * (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ Real.pi - 1 by linarith [Real.pi_gt_three]) (sq_nonneg (n : ℝ))]
  have hmul := mul_le_mul_of_nonneg_right hpi (inv_nonneg.mpr ht.le)
  rw [habs]
  simp only [div_eq_mul_inv] at hmul ⊢
  nlinarith

theorem integer_gaussian_sum_bound {t : ℝ} (ht : 0 < t) (s : Finset ℤ) :
    (∑ n ∈ s, Real.exp (-Real.pi / t * (n : ℝ) ^ 2)) ≤ 1 + 2 * t := by
  have hr0 : 0 ≤ Real.exp (-1 / t) := (Real.exp_pos _).le
  have hr1 : Real.exp (-1 / t) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) ht)
  calc
    _ ≤ ∑ n ∈ s, (Real.exp (-1 / t)) ^ n.natAbs :=
      Finset.sum_le_sum fun n _ => integer_gaussian_le_geometric n ht
    _ ≤ ∑' n : ℤ, (Real.exp (-1 / t)) ^ n.natAbs :=
      (hasSum_geometric_natAbs hr0 hr1).summable.sum_le_tsum s (fun n _ => by positivity)
    _ ≤ _ := integer_geometric_sum_bound ht

end Erdos3

end

end OAI
