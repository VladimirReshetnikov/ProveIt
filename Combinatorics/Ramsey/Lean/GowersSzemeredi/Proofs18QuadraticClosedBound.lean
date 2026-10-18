import GowersSzemeredi.Proofs18DensityIterationGrowth
import GowersSzemeredi.Proofs18QuadraticIteration

/-! Closed length bounds for the four-term interval and cyclic theorems.

`finiteInterval_hasModAP_of_hasNatAP` and `quadratic_cyclic_szemeredi_closed`
are in `Proofs18QuadraticClosedBoundSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def quadraticIntervalClosedThreshold (delta : Real) : Real :=
  densityIterationClosedThreshold (intervalQuadraticStepThreshold delta)
    (intervalQuadraticLengthFactor delta) (intervalQuadraticLengthExponent delta)
    ⌈(intervalQuadraticGain delta)⁻¹⌉₊

theorem quadraticIntervalIterationThreshold_le_closed {delta : Real} (hδ : 0 < delta) :
    quadraticIntervalIterationThreshold delta ≤ quadraticIntervalClosedThreshold delta := by
  obtain ⟨_, hρ, hc⟩ := intervalQuadratic_constants_pos hδ
  exact densityIterationThreshold_le_closed hc hρ _

theorem quadratic_interval_szemeredi_closed
    (delta : Real) (hδ : 0 < delta) (hδone : delta ≤ 1)
    (L : Nat) (hL : quadraticIntervalClosedThreshold delta ≤ L)
    (B : Finset (Fin L)) (hcard : delta * L ≤ B.card) : HasNatAP (B.image Fin.val) 4 :=
  quadratic_interval_szemeredi_recursive delta hδ hδone L
    ((quadraticIntervalIterationThreshold_le_closed hδ).trans hL) B hcard

end LeanProofs.GowersSzemeredi
