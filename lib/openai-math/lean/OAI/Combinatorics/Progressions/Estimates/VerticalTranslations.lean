import OAI.Combinatorics.Progressions.Fourier.VerticalFrequencyIdentification

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup CircleFourier

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem vertical_left_translate (F : D.Space → ℂ) (eta : L →ₗ[ℚ] ℚ)
    (hF : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
      F (z • x) = character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * F x)
    (a : D.RealGroup) (z : D.RealGroup) (hz : z ∈ D.filtration.realification.subgroup s)
    (x : D.Space) :
    F (a • (z • x)) =
      character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * F (a • x) := by
  have hc : Commute z a := commute_of_lie_eq_zero z a
    (D.filtration.realification.top_layer_central hz a.coord)
  rw [← mul_smul, hc.eq.symm, mul_smul]
  exact hF z hz (a • x)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
