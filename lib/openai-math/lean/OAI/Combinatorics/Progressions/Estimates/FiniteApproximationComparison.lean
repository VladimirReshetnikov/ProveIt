import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem indicator_comparison_le {I lower upper a b W : ℝ}
    (hW : 0 ≤ W) (ha : 0 ≤ a) (hb : b ≤ W) (hlo : lower ≤ I) (hhi : I ≤ upper) :
    I * (a - b) ≤ upper * (a - b) + W * (upper - lower) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hhi) ha,
    mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hhi),
    mul_nonneg hW (sub_nonneg.mpr hlo)]

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem mean_indicator_comparison_le (S : Finset G) (f g lower upper : G → ℝ)
    {W epsilon gamma : ℝ} (hW : 0 ≤ W) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W)
    (hsand : ∀ x, lower x ≤ (if x ∈ S then (1 : ℝ) else 0) ∧
      (if x ∈ S then (1 : ℝ) else 0) ≤ upper x)
    (hmean : (𝔼 x, upper x * (f x - g x)) ≤ epsilon)
    (hgap : (𝔼 x, (upper x - lower x)) ≤ gamma) :
    (𝔼 x, if x ∈ S then f x - g x else 0) ≤ epsilon + W * gamma := by
  calc
    _ ≤ 𝔼 x, (upper x * (f x - g x) + W * (upper x - lower x)) := by
      apply Finset.expect_le_expect
      intro x _
      have h := indicator_comparison_le hW (hf x) (hg x) (hsand x).1 (hsand x).2
      simpa only [ite_mul, one_mul, zero_mul] using h
    _ = (𝔼 x, upper x * (f x - g x)) + W * (𝔼 x, (upper x - lower x)) := by
      rw [Finset.expect_add_distrib, ← Finset.mul_expect]
    _ ≤ _ := add_le_add hmean (mul_le_mul_of_nonneg_left hgap hW)

theorem local_average_le_of_approximation (S : Finset G) (hS : S.Nonempty)
    (f g lower upper : G → ℝ) {W epsilon kappa : ℝ}
    (hW : 0 ≤ W) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W)
    (hsand : ∀ x, lower x ≤ (if x ∈ S then (1 : ℝ) else 0) ∧
      (if x ∈ S then (1 : ℝ) else 0) ≤ upper x)
    (hmean : (𝔼 x, upper x * (f x - g x)) ≤ epsilon)
    (hgap : (𝔼 x, (upper x - lower x)) ≤ kappa * ((S.card : ℝ) / Fintype.card G)) :
    (𝔼 x ∈ S, (f x - g x)) ≤ (Fintype.card G : ℝ) / S.card * epsilon + W * kappa := by
  have hSc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hGc : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast hS.card_pos.trans_le (Finset.card_le_univ S)
  have h := mean_indicator_comparison_le S f g lower upper hW hf hg hsand hmean hgap
  have heq : (𝔼 x, if x ∈ S then f x - g x else 0) =
      (S.card : ℝ) / Fintype.card G * (𝔼 x ∈ S, (f x - g x)) := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [Finset.sum_ite_mem, Finset.univ_inter]
    rw [← Finset.card_mul_expect S (fun x => f x - g x)]
    ring
  rw [heq] at h
  calc
    _ = ((Fintype.card G : ℝ) / S.card) *
        (((S.card : ℝ) / Fintype.card G) * (𝔼 x ∈ S, (f x - g x))) := by
      field_simp
    _ ≤ ((Fintype.card G : ℝ) / S.card) *
        (epsilon + W * (kappa * ((S.card : ℝ) / Fintype.card G))) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

end Erdos3

end

end OAI
