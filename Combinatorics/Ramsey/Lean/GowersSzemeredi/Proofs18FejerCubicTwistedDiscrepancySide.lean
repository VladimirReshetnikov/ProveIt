import GowersSzemeredi.Proofs18FejerCubicTwistedDiscrepancy
import GowersSzemeredi.Proofs13FejerOddSquareSide

/-! Declarations of `Proofs18FejerCubicTwistedDiscrepancy` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open scoped BigOperators

/-- Cubic nonuniformity yields a full proper discrepancy partition for one
cubic twist. The explicit count is scaled by the common original cell
length, which retains the Section 13 positive-power lower bound. -/
theorem fejer_cubic_nonuniformity_twisted_discrepancy (alpha : Real)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], fejerCubicTwistedThreshold alpha ≤ (N : Real) →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
      ∃ phi : ZMod N → ZMod N, ∃ l J : Nat, ∃ R : Fin J → ModAP N,
        PolynomialOn 3 Finset.univ phi ∧
        (N : Real) ^ fejerCubicLocalizationExponent alpha / 12 ≤ l ∧
        IsPartition (fun j => (R j).carrier) Finset.univ ∧
        (∀ j, (R j).IsProper) ∧
        (J : Real) ≤ fejerCubicLocalCountConstant alpha * N / (l : Real) ^ fejerCubicLocalCountExponent alpha ∧
        fejerCubicTwistedDiscrepancyParameter alpha * N ≤ ∑ j, ‖∑ x ∈ (R j).carrier, phaseTwist f phi x‖ := by
  exact FejerOddSquareAt.twistedDiscrepancy (theorem_13_12_fejer_odd_square_explicit alpha hα hαone :
    FejerOddSquareAt alpha (fejerCubicLocalizationExponent alpha)
      (section13FejerOddSquareThreshold alpha)) hα hαone
    (section13_fejer_explicit_exponent_bounds hα hαone).1

end

end LeanProofs.GowersSzemeredi
