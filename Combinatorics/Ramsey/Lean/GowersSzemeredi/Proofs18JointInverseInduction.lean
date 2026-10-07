import GowersSzemeredi.Proofs18JointInverseParameters

/-! Complete inverse induction using the actual joint-cover controls.
Degree n+2 requires only exact structural dimensions 2 through n. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The top structural dimension in the preceding inverse route is no
longer an input. Quadratic and improved cubic inverse bounds remain the
unconditional bases; dimension one is supplied by Lemma 16.3. -/
theorem function_inverse_of_lower_structural_dimensions (n : Nat)
    (hth : ∀ k : Nat, 2 ≤ k → k ≤ n → Theorem162At k)
    {alpha : Real} (ha : 0 < alpha) :
    ∃ T : Real, FunctionDiscrepancyBound (n + 2) alpha
      (jointStructuralInverseParameter n alpha) (jointStructuralInverseExponent n alpha) T := by
  induction n generalizing alpha with
  | zero =>
      have hbase := quadratic_function_discrepancy_bound (structuralInverseInput_pos ha)
        ((min_le_right _ _).trans (by norm_num : (1 : Real) / 2 ≤ 1))
      exact ⟨_, hbase.mono (min_le_left _ _) le_rfl (min_le_left _ _) le_rfl⟩
  | succ n ih =>
    cases n with
    | zero =>
      have hbase := fejer_cubic_function_discrepancy_bound (structuralInverseInput_pos ha)
        ((min_le_right _ _).trans (by norm_num : (1 : Real) / 2 ≤ 1))
      exact ⟨_, hbase.mono (min_le_left _ _) le_rfl (min_le_left _ _) le_rfl⟩
    | succ n =>
      obtain ⟨T, hT⟩ := ih (fun k hk hkn => hth k hk (by omega))
        (jointStructuralInverseLowerInput_pos ha (n + 2))
      have hstruct : ∀ l : Nat, 1 ≤ l → l ≤ n + 2 → Theorem162At l := by
        intro l hl hln
        by_cases h1 : l = 1
        · subst l
          exact lemma_16_3_holds
        · exact hth l (by omega) hln
      obtain ⟨Tnext, hnext⟩ := function_inverse_step_of_joint_power_structure
        (by omega : 1 ≤ n + 2) hstruct (structuralInverseInput_pos ha) (min_le_right _ _) hT
        (jointStructuralInverseParameter_pos (n + 1) (jointStructuralInverseLowerInput_pos ha (n + 2)))
        (jointStructuralInverseExponent_pos (n + 1) (jointStructuralInverseLowerInput_pos ha (n + 2)))
        ((jointStructuralInverseExponent_le_one _ _).trans (by norm_num))
      exact ⟨Tnext, hnext.mono (min_le_left _ _) le_rfl (min_le_left _ _) le_rfl⟩

/-- The quartic inverse theorem needs only the unresolved exact bilinear
structural theorem. No dimension-three structural theorem is assumed. -/
theorem quartic_function_inverse_of_bilinear_structure (hth : Theorem162At 2)
    {alpha : Real} (ha : 0 < alpha) :
    ∃ T : Real, FunctionDiscrepancyBound 4 alpha
      (jointStructuralInverseParameter 2 alpha) (jointStructuralInverseExponent 2 alpha) T := by
  apply function_inverse_of_lower_structural_dimensions 2 _ ha
  intro k hk hk2
  have heq : k = 2 := by omega
  simpa only [heq] using hth

end LeanProofs.GowersSzemeredi
