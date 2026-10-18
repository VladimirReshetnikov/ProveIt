import GowersSzemeredi.Proofs13FejerOddSquare
import GowersSzemeredi.Proofs13FejerExplicitExponentSide

/-! Declarations of `Proofs13FejerOddSquare` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The explicit Fourier extraction exponent lies in (0,1/2]. -/
theorem section13_fejer_explicit_exponent_bounds {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    0 < (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53)) ∧
      (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53)) ≤ 1 / 2 := by
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  have ht : (1 : Real) ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hexp := one_le_pow₀ ht (n := (2 : Nat) ^ 53)
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
    (by norm_num : (0 : Real) < 1 / 2) (by norm_num : (1 / 2 : Real) ≤ 1) hexp

end LeanProofs.GowersSzemeredi

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
