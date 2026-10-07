import OAI.Combinatorics.Progressions.Polynomial.MajorTranslationPolynomialSymbolDegree

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {U B : Type*}

theorem majorTranslationJointPolynomial_lower (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLT (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) :
    majorTranslationJointPolynomial D A ∈
      weightedSupportLT (Sum.elim (fun _ : U => 1) w) d := by
  rw [majorTranslationJointPolynomial_eq_sub_aeval]
  apply (weightedSupportLT _ _).sub_mem hD
  apply weightedSupportLT_aeval _ _ _ _ hD
  intro i
  cases i with
  | inl i => exact Submodule.zero_mem _
  | inr j =>
      exact (weightedSupportLE _ _).sub_mem
        (weightedSupportLE_X (Sum.elim (fun _ : U => 1) w) (Sum.inr j))
        (majorParameterRename_degree (fun _ => 1) w
          ((mem_weightedSupportLE_one_iff (A j) (w j)).mpr (hA j)))

theorem majorTranslationJointPolynomial_sub
    (D E : MvPolynomial (U ⊕ B) ℝ) (A : B → MvPolynomial U ℝ) :
    majorTranslationJointPolynomial (D - E) A =
      majorTranslationJointPolynomial D A - majorTranslationJointPolynomial E A := by
  simp only [majorTranslationJointPolynomial_eq_sub_aeval, map_sub]
  abel

end Erdos3

end

end OAI
