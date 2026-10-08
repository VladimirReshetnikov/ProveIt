import GowersSzemeredi.Proofs16DimensionTwo
import GowersSzemeredi.Proofs18JointInverseInduction
import GowersSzemeredi.Proofs18GeneralIteration

/-! The proved two-dimensional structural theorem discharges the quartic
inverse input and the six-term density iteration. The inverse threshold
remains existential; no closed six-term numerical improvement is claimed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- An unconditional quartic function inverse theorem, with the explicit
joint structural parameters and a threshold depending only on alpha. -/
theorem quartic_function_discrepancy_bound {alpha : Real} (ha : 0 < alpha) :
    ∃ T : Real, FunctionDiscrepancyBound 4 alpha
      (jointStructuralInverseParameter 2 alpha) (jointStructuralInverseExponent 2 alpha) T :=
  quartic_function_inverse_of_bilinear_structure theorem_16_2_at_two ha

/-- The six-term density iteration now has no structural or inverse premise.
Its closed iteration formula still depends on an existential threshold T. -/
theorem natural_six_term_via_quartic_inverse (delta : Real)
    (hd : 0 < delta) : ∃ T : Real,
    ∀ N : Nat,
      intervalDiscrepancyClosedThreshold 6 delta
        (jointStructuralInverseParameter 2 (intervalUniformityParameter delta 6))
        (jointStructuralInverseExponent 2 (intervalUniformityParameter delta 6)) T ≤ N →
      ∀ A : Finset Nat, A ⊆ Finset.Icc 1 N → delta * N ≤ A.card → HasNatAP A 6 := by
  have ha := intervalUniformityParameter_pos (k := 6) hd (by omega)
  obtain ⟨T, hT⟩ := quartic_function_discrepancy_bound ha
  refine ⟨T, fun N hN A hA hcard => ?_⟩
  exact hT.natural_szemeredi_closed (by omega) hd
    (jointStructuralInverseParameter_pos 2 ha)
    (jointStructuralInverseExponent_pos 2 ha) N hN A hA hcard

end LeanProofs.GowersSzemeredi
