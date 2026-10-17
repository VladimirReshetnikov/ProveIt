import GowersSzemeredi.Proofs17FejerCubicLocalization
import GowersSzemeredi.Proofs13FejerOddSquareSide

/-! Declarations of `Proofs17FejerCubicLocalization` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem fejer_cubic_nonuniformity_localized_phase_removal :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 →
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], section13FejerOddSquareThreshold alpha ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ phi : ZMod N → ZMod N, ∃ M l : Nat, ∃ Q : Fin M → ModAP N,
          PolynomialOn 3 Finset.univ phi ∧
          IsPartition (fun i => (Q i).carrier) Finset.univ ∧
          (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53))) / 12 ≤ l ∧
          (∀ i, ((Q i).length : Real) ≤ Real.sqrt N) ∧
          ¬ UniformOnPartition (phaseTwist f phi) 2
            ((2 : Real) ^ (-(58 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 42)) Q (l + 1) := by
  intro alpha hα hαone
  exact FejerOddSquareAt.localized (theorem_13_12_fejer_odd_square_explicit alpha hα hαone :
    FejerOddSquareAt alpha ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53)))
      (section13FejerOddSquareThreshold alpha)) hα

end LeanProofs.GowersSzemeredi
