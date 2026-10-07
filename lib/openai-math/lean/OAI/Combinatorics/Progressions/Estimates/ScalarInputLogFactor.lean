import OAI.Combinatorics.Progressions.Dynamics.InitialBudgetJointReplacement

namespace OAI

section

namespace Erdos3

theorem exists_scalarInputLogFactor (ell : ℕ) (epsilon : ℝ) :
    ∃ A0 : ℕ, 10 ≤ A0 ∧ epsilon⁻¹ ≤ Real.exp (A0 : ℝ) ∧
      (ell : ℝ) ≤ Real.exp (A0 : ℝ) ∧
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp (A0 : ℝ) := by
  let B : ℝ := max 10 (max epsilon⁻¹ (max (ell : ℝ) (probabilityProfileLipschitz : ℝ)))
  obtain ⟨A0, hA0⟩ := exists_nat_ge B
  have h10 : (10 : ℝ) ≤ A0 := (le_max_left _ _).trans hA0
  have hexp : (A0 : ℝ) ≤ Real.exp (A0 : ℝ) := by linarith [Real.add_one_le_exp (A0 : ℝ)]
  refine ⟨A0, by exact_mod_cast h10, ?_, ?_, ?_⟩
  · exact ((le_max_left _ _).trans ((le_max_right _ _).trans hA0)).trans hexp
  · exact ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hA0))).trans hexp
  · exact ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hA0))).trans hexp

end Erdos3

end

end OAI
