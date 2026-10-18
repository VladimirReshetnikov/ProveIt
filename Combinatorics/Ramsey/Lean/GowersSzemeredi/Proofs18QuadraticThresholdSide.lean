import GowersSzemeredi.Proofs18QuadraticThreshold
import GowersSzemeredi.Proofs18QuadraticDensityIncrementSide

/-! Declarations of `Proofs18QuadraticThreshold` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- Explicit-threshold quadratic density increment, without an assumed
inverse theorem or an opaque sufficiently-large modulus. -/
theorem quadratic_nonuniformity_density_increment_explicit
    (alpha : Real) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (N : Nat) [NeZero N] [Fact N.Prime] (hN : quadraticDensityThreshold alpha ≤ N)
    (A : Finset (ZMod N)) (hnot : ¬ UniformSetOfDegree A alpha 2) :
    ∃ P : ModAP N, P.IsProper ∧
      quadraticDiscrepancyParameter alpha / 4 * (N : Real) ^ quadraticDiscrepancyExponent alpha ≤
        (P.carrier.card : Real) ∧
      (density A + quadraticDiscrepancyParameter alpha / 4) * P.carrier.card ≤ (A ∩ P.carrier).card := by
  obtain ⟨M, P, hpart, hproper, havg, hdis⟩ :=
    quadratic_nonuniformity_discrepancy_partition_explicit alpha hα hαone N hN
      (balanced A) (balanced_discValued A) hnot
  have hβ : 0 ≤ quadraticDiscrepancyParameter alpha := by
    unfold quadraticDiscrepancyParameter
    positivity
  obtain ⟨j, hsize, hinc⟩ := density_increment_of_discrepancy_partition A P _ _ hβ hpart havg hdis
  exact ⟨P j, hproper j, hsize, hinc⟩

end LeanProofs.GowersSzemeredi
