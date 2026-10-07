import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_model_test_difference {V I : Type*} [AddCommGroup V] [Module ℂ V] [Fintype I]
    (A B : V →ₗ[ℂ] ℂ) (v e : V) (J : I → V) (c : I → ℂ)
    (hmodel : v = (∑ i, c i • J i) + e) {M η α β : ℝ}
    (hη : 0 ≤ η) (hc : (∑ i, ‖c i‖) ≤ M)
    (hatom : ∀ i, ‖A (J i) - B (J i)‖ ≤ η)
    (heA : ‖A e‖ ≤ α) (heB : ‖B e‖ ≤ β) :
    ‖A v - B v‖ ≤ M * η + α + β := by
  have hid : A v - B v = (∑ i, c i * (A (J i) - B (J i))) + (A e - B e) := by
    rw [hmodel, map_add, map_add, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    abel
  have hsum : ‖∑ i, c i * (A (J i) - B (J i))‖ ≤ M * η := by
    calc
      _ ≤ ∑ i, ‖c i * (A (J i) - B (J i))‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * η := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hatom i) (norm_nonneg _)
      _ = (∑ i, ‖c i‖) * η := (Finset.sum_mul _ _ _).symm
      _ ≤ M * η := mul_le_mul_of_nonneg_right hc hη
  rw [hid]
  exact (norm_add_le _ _).trans ((add_le_add hsum
    ((norm_sub_le _ _).trans (add_le_add heA heB))).trans_eq (by ring))

theorem finite_model_score_transfer {V I : Type*} [AddCommGroup V] [Module ℂ V] [Fintype I]
    (A B : V →ₗ[ℂ] ℂ) (v e : V) (J : I → V) (c : I → ℂ)
    (hmodel : v = (∑ i, c i • J i) + e) {M η α β S : ℝ}
    (hη : 0 ≤ η) (hc : (∑ i, ‖c i‖) ≤ M)
    (hatom : ∀ i, ‖A (J i) - B (J i)‖ ≤ η)
    (heA : ‖A e‖ ≤ α) (heB : ‖B e‖ ≤ β) (hscore : S ≤ (B v).re) :
    S - (M * η + α + β) ≤ (A v).re := by
  have hnorm := finite_model_test_difference A B v e J c hmodel hη hc hatom heA heB
  have hre := (neg_le_abs ((A v - B v).re)).trans
    ((Complex.abs_re_le_norm _).trans hnorm)
  simp only [Complex.sub_re] at hre
  linarith

end Erdos3

end

end OAI
