import GowersSzemeredi.Proofs18GeneralLocalInverseAssembly
import GowersSzemeredi.Proofs18FejerCubicParameters
import GowersSzemeredi.Proofs18FejerCubicAt

/-! Explicit modulus threshold for the global cubic twisted discrepancy partition. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

def fejerCubicTwistedThreshold (alpha : Real) : Real :=
  fejerCubicPrimeModelThreshold alpha
    (max 4 (quadraticExponentialThreshold (fejerCubicLocalQuadraticParameter alpha)))

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

end LeanProofs.GowersSzemeredi
