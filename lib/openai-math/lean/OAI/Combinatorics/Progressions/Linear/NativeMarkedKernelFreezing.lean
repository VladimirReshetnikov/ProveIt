import OAI.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest
open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L Q : Type*} [LieRing L] [LieAlgebra ℚ L] [Group Q] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem observable_freeze_marked_kernel_factors
    (T : D.Niltest w) (π : D.RealGroup →* Q) (ρ : Q → D.RealGroup)
    (hρ : Function.RightInverse ρ π)
    (a b r : D.RealGroup) (aF rF : Q)
    (kE kR : D.RealGroup) (hkE : π kE = 1) (hkR : π kR = 1)
    (hcoset : (QuotientGroup.mk ((ρ rF)⁻¹ * r) : D.Space) = QuotientGroup.mk kR) :
    π (kE * ρ aF) = aF ∧ π (ρ rF * kR) = rF ∧
      letI := rightMetricSpace
        (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      ‖T.observable (QuotientGroup.mk (a * b * r)) -
        T.observable (QuotientGroup.mk ((kE * ρ aF) * b * (ρ rF * kR)))‖ ≤
          (T.lipBound : ℝ) * dist (a * (ρ aF)⁻¹) kE := by
  let := rightMetricSpace
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  have hright : (QuotientGroup.mk r : D.Space) = QuotientGroup.mk (ρ rF * kR) := by
    have h := congrArg (fun x : D.Space => (ρ rF) • x) hcoset
    change QuotientGroup.mk (ρ rF * ((ρ rF)⁻¹ * r)) =
      (QuotientGroup.mk (ρ rF * kR) : D.Space) at h
    simpa only [mul_inv_cancel_left] using h
  refine ⟨by rw [map_mul, hkE, hρ, one_mul], by rw [map_mul, hkR, hρ, mul_one], ?_⟩
  have hfreeze := T.observable_freeze_factors a (kE * ρ aF) b r (ρ rF * kR) hright
  have hdist : dist a (kE * ρ aF) = dist (a * (ρ aF)⁻¹) kE := by
    rw [← dist_mul_right a (kE * ρ aF) (ρ aF)⁻¹, mul_inv_cancel_right]
  exact hfreeze.trans_eq (congrArg (fun z : ℝ => (T.lipBound : ℝ) * z) hdist)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
