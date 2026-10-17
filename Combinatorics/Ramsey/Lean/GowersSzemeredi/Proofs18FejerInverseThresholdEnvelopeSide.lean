import GowersSzemeredi.Proofs18FejerInverseThresholdEnvelope
import GowersSzemeredi.Proofs18FejerCubicDiscrepancySide

/-! Declarations of `Proofs18FejerInverseThresholdEnvelope` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The complete improved cubic inverse interface at its conventional
numerical threshold, ready for the density-increment iteration. -/
theorem fejer_cubic_function_discrepancy_bound_double_exp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    FunctionDiscrepancyBound 3 alpha (fejerCubicDiscrepancyParameter alpha)
      (fejerCubicDiscrepancyExponent alpha)
      (Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 62)))) := by
  intro N _ _ hN f hf hnot
  exact fejer_cubic_function_discrepancy_bound hα hαone N
    ((fejerCubicInverseThreshold_le_double_exp hα hαone).trans hN) f hf hnot

end LeanProofs.GowersSzemeredi
