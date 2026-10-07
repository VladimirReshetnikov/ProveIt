import OAI.Combinatorics.Progressions.Estimates.NativeResidualMultiplier
import OAI.Combinatorics.Progressions.Geometry.NativeCoordinateFiber

namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeVectorCorrelation

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

theorem mean_correlation_of_degree_zero {I : Type*} {N : ℕ} [NeZero N] {p : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation 0 N p f) :
    Real.exp (-(2 * p)) ≤ ‖𝔼 x, f W.coordinate x‖ := by
  let c := W.test.observable (QuotientGroup.mk (1 : W.model.RealGroup))
  have hnorm : ‖c‖ ≤ Real.exp p := by
    have h := W.test.eval_budget W.complexity (0 : Unit → ℤ)
    rwa [RationalFilteredNilmanifold.Niltest.eval_step_zero] at h
  have heq : (𝔼 x, f W.coordinate x * star (W.test.evalCyclic N (fun _ => x))) =
      (𝔼 x, f W.coordinate x) * star c := by
    simp only [RationalFilteredNilmanifold.Niltest.evalCyclic,
      RationalFilteredNilmanifold.Niltest.eval_step_zero, ← Finset.expect_mul]
    rfl
  have h := W.correlation
  rw [heq, norm_mul, norm_star] at h
  have hbound : Real.exp (-(2 * p)) * Real.exp p ≤ ‖𝔼 x, f W.coordinate x‖ * Real.exp p := by
    rw [← Real.exp_add, show -(2 * p) + p = -p by ring]
    exact h.trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
  exact le_of_mul_le_mul_right hbound (Real.exp_pos p)

end NativeVectorCorrelation

namespace NativeMixedCorrelation

theorem exists_fixed_quadratic_coordinate {N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (W : NativeMixedCorrelation 1 N p f) :
    ∃ i : Fin W.mixed.outputDim, ∃ H ⊆ W.shifts, H.Nonempty ∧
      Real.exp (-(2 * p)) * N ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, Real.exp (-(2 * p)) ≤
        ‖𝔼 x, multiplicativeDerivative f h x * star (W.mixed.evalCyclic N i (correlationInput h x))‖ := by
  obtain ⟨i, H, hsub, hH, hdense, hcorr⟩ := NativeVectorCorrelation.exists_fixed_coordinate
    W.shifts W.nonempty (nativeMixedResidual f W.mixed)
    (by simpa only [Fintype.card_fin] using W.mixed.output_bound) W.correlation
  refine ⟨i, H, hsub, hH, ?_, ?_⟩
  · have hW : Real.exp (-p) * N ≤ (W.shifts.card : ℝ) := by
      simpa only [ZMod.card] using W.density
    calc
      Real.exp (-(2 * p)) * N = Real.exp (-p) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-p) * W.shifts.card := mul_le_mul_of_nonneg_left hW (Real.exp_nonneg _)
      _ ≤ H.card := hdense
  · intro h hh
    obtain ⟨V⟩ := hcorr h hh
    exact V.mean_correlation_of_degree_zero

end NativeMixedCorrelation

end Erdos3

end

end OAI
