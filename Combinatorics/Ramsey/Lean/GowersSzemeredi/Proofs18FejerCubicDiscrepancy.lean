import GowersSzemeredi.Proofs18GeneralPhaseInverseAssembly
import GowersSzemeredi.Proofs18FejerCubicParameters
import GowersSzemeredi.Proofs18FejerCubicTwistedDiscrepancy

/-! A fully explicit threshold for the cubic function inverse theorem. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

def fejerCubicInverseThreshold (alpha : Real) : Real :=
  max (fejerCubicTwistedThreshold alpha)
    (positivePowerThreshold (fejerCubicPhaseRefinementConstant alpha) 1
      (fejerCubicDiscrepancyExponent alpha))

/-- Every disc-valued function failing cubic uniformity has an untwisted
proper discrepancy partition, with explicit positive discrepancy and average
size parameters and an explicit modulus threshold. -/
theorem fejer_cubic_nonuniformity_discrepancy_partition (alpha : Real)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], fejerCubicInverseThreshold alpha ≤ (N : Real) →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
      ∃ J : Nat, ∃ R : Fin J → ModAP N,
        IsPartition (fun j => (R j).carrier) Finset.univ ∧
        (∀ j, (R j).IsProper) ∧
        (N : Real) ^ fejerCubicDiscrepancyExponent alpha ≤ averageCellSize (fun j => (R j).carrier) ∧
        fejerCubicDiscrepancyParameter alpha * N ≤ ∑ j, ‖∑ x ∈ (R j).carrier, f x‖ := by
  exact FejerOddSquareAt.functionDiscrepancyBound (theorem_13_12_fejer_odd_square_explicit alpha hα hαone :
    FejerOddSquareAt alpha (fejerCubicLocalizationExponent alpha)
      (section13FejerOddSquareThreshold alpha)) hα hαone
    (section13_fejer_explicit_exponent_bounds hα hαone).1

/-- The cubic inverse interface with every threshold specified by a finite formula. -/
theorem fejer_cubic_function_discrepancy_bound {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    FunctionDiscrepancyBound 3 alpha (fejerCubicDiscrepancyParameter alpha)
      (fejerCubicDiscrepancyExponent alpha) (fejerCubicInverseThreshold alpha) := by
  intro N _ _ hN f hf hnot
  exact fejer_cubic_nonuniformity_discrepancy_partition alpha hα hαone N hN f hf hnot

end LeanProofs.GowersSzemeredi
