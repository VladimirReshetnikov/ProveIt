import GowersSzemeredi.Proofs18IntervalDiscrepancyIncrement
import GowersSzemeredi.Proofs18QuadraticDichotomy

/-! A quadratic density increment on a proper progression contained in the
original interval. The original relative density is retained. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Refining away interval-boundary crossings gives a genuine progression
inside the support, with explicit size and relative-density increment. -/
theorem interval_quadratic_density_increment
    (alpha : Real) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (N L : Nat) [NeZero N] [Fact N.Prime] (hL : L ≤ N)
    (hN : quadraticExponentialThreshold alpha ≤ N)
    (hscale : 32 ≤ quadraticDiscrepancyParameter alpha * N)
    (A : Finset (ZMod N)) (delta : Real)
    (hAS : A ⊆ finiteIntervalImage N (Finset.univ : Finset (Fin L)))
    (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hcard : (A.card : Real) = delta * L)
    (hnot : ¬ UniformOfDegree
      (relativeBalanced A (finiteIntervalImage N (Finset.univ : Finset (Fin L))) delta) alpha 2) :
    ∃ P : ModAP N, P.IsProper ∧
      P.carrier ⊆ finiteIntervalImage N (Finset.univ : Finset (Fin L)) ∧
      (quadraticDiscrepancyParameter alpha /
          (8 * boundaryRefinementConstant (quadraticDiscrepancyParameter alpha / 64))) *
        (N : Real) ^ (quadraticDiscrepancyExponent alpha / 16) ≤ (P.carrier.card : Real) ∧
      (delta + quadraticDiscrepancyParameter alpha / 8) * P.carrier.card ≤ (A ∩ P.carrier).card := by
  obtain ⟨M, Q, hQ, hQproper, havg, hdis⟩ :=
    quadratic_nonuniformity_discrepancy_partition_explicit alpha hα hαone N
      ((quadraticDensityThreshold_le_exp_power hα hαone).trans hN)
      (relativeBalanced A (finiteIntervalImage N (Finset.univ : Finset (Fin L))) delta)
      (relativeBalanced_discValued A _ delta hAS hδ hδone) hnot
  exact interval_density_increment_of_discrepancy_partition hL
    (quadraticDiscrepancyParameter alpha) (quadraticDiscrepancyExponent alpha)
    (by unfold quadraticDiscrepancyParameter; positivity) hscale A delta hAS hδ hδone hcard
    Q hQ hQproper havg hdis

end LeanProofs.GowersSzemeredi
