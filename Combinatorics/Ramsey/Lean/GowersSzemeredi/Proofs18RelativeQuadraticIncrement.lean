import GowersSzemeredi.Proofs18RelativeBalance
import GowersSzemeredi.Proofs18QuadraticDichotomy

/-! The explicit quadratic increment for density relative to a support. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Relative quadratic nonuniformity gives an increment without replacing
the support density by ambient density. The increment is on S intersect P;
extracting an ordinary progression requires further support geometry. -/
theorem quadratic_relative_density_increment_on_intersection
    (alpha : Real) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (N : Nat) [NeZero N] [Fact N.Prime] (hN : quadraticExponentialThreshold alpha ≤ N)
    (A S : Finset (ZMod N)) (delta : Real)
    (hAS : A ⊆ S) (hδ : 0 ≤ delta) (hδone : delta ≤ 1)
    (hcard : (A.card : Real) = delta * S.card)
    (hnot : ¬ UniformOfDegree (relativeBalanced A S delta) alpha 2) :
    ∃ P : ModAP N, P.IsProper ∧
      quadraticDiscrepancyParameter alpha / 4 * (N : Real) ^ quadraticDiscrepancyExponent alpha ≤
        (P.carrier.card : Real) ∧
      (quadraticDiscrepancyParameter alpha / 4) ^ 2 * (N : Real) ^ quadraticDiscrepancyExponent alpha ≤
        ((S ∩ P.carrier).card : Real) ∧
      (delta + quadraticDiscrepancyParameter alpha / 4) * (S ∩ P.carrier).card ≤
        (A ∩ P.carrier).card := by
  obtain ⟨M, P, hpart, hproper, havg, hdis⟩ :=
    quadratic_nonuniformity_discrepancy_partition_explicit alpha hα hαone N
      ((quadraticDensityThreshold_le_exp_power hα hαone).trans hN)
      (relativeBalanced A S delta) (relativeBalanced_discValued A S delta hAS hδ hδone) hnot
  have hβ : 0 ≤ quadraticDiscrepancyParameter alpha := by
    unfold quadraticDiscrepancyParameter
    positivity
  obtain ⟨j, hsize, hsupport, hinc⟩ := relative_density_increment_of_discrepancy_partition
    A S delta _ _ P hAS hδ hδone hβ hcard hpart havg hdis
  exact ⟨P j, hproper j, hsize, hsupport, hinc⟩

end LeanProofs.GowersSzemeredi
