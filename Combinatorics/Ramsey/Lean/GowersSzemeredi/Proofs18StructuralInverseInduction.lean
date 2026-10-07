import GowersSzemeredi.Proofs18StructuralInverseParameters

/-! Complete the induction in the uniformity degree. The only unproved
inputs are the finitely many required dimensions of the Section 16
structural theorem. No localization or lower-degree inverse is assumed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Every degree n+2 has a positive discrepancy and partition-size power,
with the displayed recursive parameters. Only structural dimensions from
three through n+1 are needed; the quadratic and improved cubic base cases
are unconditional. -/
theorem function_inverse_of_structural_dimensions (n : Nat)
    (hth : ∀ k : Nat, 3 ≤ k → k < n + 2 → Theorem162At k)
    {alpha : Real} (hα : 0 < alpha) :
    ∃ T : Real, FunctionDiscrepancyBound (n + 2) alpha
      (structuralInverseParameter n alpha) (structuralInverseExponent n alpha) T := by
  induction n generalizing alpha with
  | zero =>
      have hbase := quadratic_function_discrepancy_bound (structuralInverseInput_pos hα)
        ((min_le_right _ _).trans (by norm_num : (1 : Real) / 2 ≤ 1))
      exact ⟨_, hbase.mono (min_le_left _ _) le_rfl (min_le_left _ _) le_rfl⟩
  | succ n ih =>
    cases n with
    | zero =>
      have hbase := fejer_cubic_function_discrepancy_bound (structuralInverseInput_pos hα)
        ((min_le_right _ _).trans (by norm_num : (1 : Real) / 2 ≤ 1))
      exact ⟨_, hbase.mono (min_le_left _ _) le_rfl (min_le_left _ _) le_rfl⟩
    | succ n =>
      obtain ⟨T, hT⟩ := ih (fun k hk hkn => hth k hk (by omega))
        (structuralInverseLowerInput_pos hα (n + 3))
      obtain ⟨Tnext, hnext⟩ := function_inverse_step_of_dimension_induction
        (by omega : 1 ≤ n + 3) (hth (n + 3) (by omega) (by omega))
        (structuralInverseInput_pos hα) (min_le_right _ _) hT
        (structuralInverseParameter_pos (n + 1) (structuralInverseLowerInput_pos hα (n + 3)))
        (structuralInverseExponent_pos (n + 1) (structuralInverseLowerInput_pos hα (n + 3)))
        ((structuralInverseExponent_le_one _ _).trans (by norm_num))
      exact ⟨Tnext, hnext.mono (min_le_left _ _) le_rfl (min_le_left _ _) le_rfl⟩

end LeanProofs.GowersSzemeredi
