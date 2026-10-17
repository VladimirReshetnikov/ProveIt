import GowersSzemeredi.Proofs13FejerOddSquare
import GowersSzemeredi.Proofs13FejerExplicitExponentSide

/-! Declarations of `Proofs13FejerOddSquare` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem theorem_13_12_fejer_odd_square_explicit :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 →
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], section13FejerOddSquareThreshold alpha ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ m : Nat, ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          Odd m ∧ 0 < m ∧ (m : Real) ≤ Real.sqrt N ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53))) / 2 ≤ m ∧
          P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = m ∧ Q.length = m ∧
          B ⊆ P.carrier.product Q.carrier ∧
          (alpha / 2) ^ ((2 : Nat) ^ 42) / 4 * m * m ≤ B.card ∧
          BilinearOn (P.carrier.product Q.carrier) phi ∧
          ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  intro alpha hα hαone
  exact FejerSquareAt.oddSquare (theorem_13_12_fejer_explicit_threshold alpha hα hαone :
    FejerSquareAt alpha ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53)))
      (section13FourierThreshold alpha)) hα
    (section13_fejer_explicit_exponent_bounds hα hαone).1
    (section13_fejer_explicit_exponent_bounds hα hαone).2

end LeanProofs.GowersSzemeredi
