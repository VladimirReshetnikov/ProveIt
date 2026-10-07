import GowersSzemeredi.Proofs18StructuralInverseInduction
import GowersSzemeredi.Proofs18GeneralIteration

/-! Consequences of the completed inverse induction with its actual
recursive parameters. No comparison with the source's headline tower
bound is asserted here. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- A common positive constant can be used for both average cell size and
discrepancy, as in the form of Theorem 18.1. -/
def structuralInverseCommonParameter (n : Nat) (alpha : Real) : Real :=
  min (structuralInverseParameter n alpha) (structuralInverseExponent n alpha)

theorem structuralInverseCommonParameter_pos (n : Nat) {alpha : Real} (hα : 0 < alpha) :
    0 < structuralInverseCommonParameter n alpha :=
  lt_min (structuralInverseParameter_pos n hα) (structuralInverseExponent_pos n hα)

/-- The structural theorem in just the required dimensions yields a
balanced-set inverse theorem. The constant is the proved recursive one,
rather than the unsupported source tower estimate. -/
theorem balanced_inverse_of_structural_dimensions (n : Nat)
    (hth : ∀ k : Nat, 3 ≤ k → k < n + 2 → Theorem162At k)
    {alpha : Real} (hα : 0 < alpha) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ A : Finset (ZMod N), ¬ UniformSetOfDegree A alpha (n + 2) →
        ∃ M : Nat, ∃ Q : Fin M → ModAP N,
          IsPartition (fun i => (Q i).carrier) Finset.univ ∧
          (∀ i, (Q i).IsProper) ∧
          (N : Real) ^ structuralInverseCommonParameter n alpha ≤
            averageCellSize (fun i => (Q i).carrier) ∧
          structuralInverseCommonParameter n alpha * N ≤
            ∑ i, ‖∑ x ∈ (Q i).carrier, balanced A x‖ := by
  obtain ⟨T, hT⟩ := function_inverse_of_structural_dimensions n hth hα
  have hcommon : FunctionDiscrepancyBound (n + 2) alpha
      (structuralInverseCommonParameter n alpha) (structuralInverseCommonParameter n alpha) T :=
    hT.mono le_rfl (min_le_left _ _) (min_le_right _ _) le_rfl
  refine ⟨⌈T⌉₊, fun N _ _ hN A hnot => ?_⟩
  exact hcommon N ((Nat.le_ceil T).trans (by exact_mod_cast hN))
    (balanced A) (balanced_discValued A) hnot

/-- Complete the Gowers density iteration for length n+4 using only
structural dimensions 3,...,n+1. The finite inverse threshold is retained
inside the explicit closed density-iteration formula. -/
theorem natural_szemeredi_of_structural_dimensions (n : Nat)
    (hth : ∀ k : Nat, 3 ≤ k → k < n + 2 → Theorem162At k)
    {delta : Real} (hδ : 0 < delta) :
    ∃ T : Real,
      FunctionDiscrepancyBound (n + 2) (intervalUniformityParameter delta (n + 4))
        (structuralInverseParameter n (intervalUniformityParameter delta (n + 4)))
        (structuralInverseExponent n (intervalUniformityParameter delta (n + 4))) T ∧
      ∀ N : Nat,
        intervalDiscrepancyClosedThreshold (n + 4) delta
          (structuralInverseParameter n (intervalUniformityParameter delta (n + 4)))
          (structuralInverseExponent n (intervalUniformityParameter delta (n + 4))) T ≤ N →
        ∀ A : Finset Nat, A ⊆ Finset.Icc 1 N → delta * N ≤ A.card → HasNatAP A (n + 4) := by
  have hα := intervalUniformityParameter_pos (k := n + 4) hδ (by omega)
  obtain ⟨T, hT⟩ := function_inverse_of_structural_dimensions n hth hα
  refine ⟨T, hT, ?_⟩
  have hdegree : n + 4 - 2 = n + 2 := by omega
  have hT' : FunctionDiscrepancyBound (n + 4 - 2) (intervalUniformityParameter delta (n + 4))
      (structuralInverseParameter n (intervalUniformityParameter delta (n + 4)))
      (structuralInverseExponent n (intervalUniformityParameter delta (n + 4))) T := by
    rw [hdegree]
    exact hT
  exact fun N hN A hA hcard => hT'.natural_szemeredi_closed (by omega) hδ
    (structuralInverseParameter_pos n hα) (structuralInverseExponent_pos n hα) N hN A hA hcard

end LeanProofs.GowersSzemeredi
