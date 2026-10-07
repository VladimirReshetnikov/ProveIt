import GowersSzemeredi.Proofs13EndpointFiniteError

/-! Intersect agreement with a concentration cutoff, losing at most
 the disagreement fraction plus four times the mean nonnegative defect. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem endpoint_good_set_card {A H : Type*} [Fintype A] [Nonempty A]
    [DecidableEq A] [DecidableEq H] (phi psi : A → H) (t : A → Real) (ht : ∀ a, 0 ≤ t a) :
    ∃ B : Finset A, (1 - endpointError phi psi - 4 * (𝔼 a : A, t a)) * Fintype.card A ≤ B.card ∧
      ∀ a ∈ B, phi a = psi a ∧ t a ≤ 1 / 4 := by
  classical
  let B := Finset.univ.filter (fun a => phi a = psi a ∧ t a ≤ 1 / 4)
  have hp (a : A) : 1 - (if phi a = psi a then (0 : Real) else 1) - 4 * t a ≤
      if a ∈ B then 1 else 0 := by
    by_cases he : phi a = psi a
    · by_cases hsmall : t a ≤ 1 / 4
      · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, he, hsmall, and_self, if_true, sub_zero]
        linarith only [ht a]
      · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, he, hsmall, and_false, if_false, if_true, sub_zero]
        linarith only [lt_of_not_ge hsmall]
    · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, he, false_and, if_false, sub_self, zero_sub]
      linarith only [ht a]
  have havg := Finset.expect_le_expect (fun a (_ : a ∈ (Finset.univ : Finset A)) => hp a)
  rw [Finset.expect_sub_distrib, Finset.expect_sub_distrib, Fintype.expect_const,
    ← Finset.mul_expect] at havg
  have hb : (𝔼 a : A, if a ∈ B then (1 : Real) else 0) = (B.card : Real) / Fintype.card A := by
    rw [Fintype.expect_eq_sum_div_card]
    congr 1
    simp
  rw [hb] at havg
  refine ⟨B, ?_, ?_⟩
  · exact (le_div_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : Real) < Fintype.card A)).mp havg
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

end LeanProofs.GowersSzemeredi
