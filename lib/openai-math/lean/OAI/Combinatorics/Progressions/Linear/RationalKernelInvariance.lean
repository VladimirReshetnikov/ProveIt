import OAI.Combinatorics.Progressions.Estimates.RationalCentralCircle

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem invariant_of_kernel_circles (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (b : Basis ι ℚ K) (f : D.Space → ℂ)
    (hf : let := D.metricSpace; ∀ i t x,
      f ((D.centralRationalCircle (b i) (hK (b i).property)).act t x) = f x)
    (z : D.RealGroup) (hz : z.coord ∈ K.baseChange ℝ) (x : D.Space) :
    f (z • x) = f x := by
  let := D.metricSpace
  have hspan : Submodule.span ℝ (Set.range (fun i => D.periodicRealDirection (b i))) =
      K.baseChange ℝ :=
    (D.periodicRealDirection_span (fun i => (b i : L))).trans
      (real_span_rational_family K (fun i => (b i : L)) (span_submodule_basis K b))
  have h := central_span_character (fun i => D.periodicRealDirection (b i))
    (fun i => D.periodicRealDirection_central (b i) (hK (b i).property))
    (0 : (ℝ ⊗[ℚ] L) →ₗ[ℝ] ℝ) f (fun i r y => by
      have hi := hf i (r : CircleFourier.Circle) y
      rw [D.centralRationalCircle_act_coe] at hi
      simpa only [LinearMap.zero_apply, mul_zero, AddCircle.coe_zero, character_zero, one_mul] using hi)
    (hspan.symm ▸ hz) x
  simpa only [LinearMap.zero_apply, AddCircle.coe_zero, character_zero, one_mul] using h

end Erdos3.RationalFilteredNilmanifold

end

end OAI
