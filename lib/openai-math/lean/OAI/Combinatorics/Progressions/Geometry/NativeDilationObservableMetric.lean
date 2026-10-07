import OAI.Combinatorics.Progressions.Estimates.NativeDilationObservable

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitz_signed_tensor_cross_product {X : Type*} [PseudoMetricSpace X]
    (m : ℤ) (f₀ : X → ℂ) (f : Fin m.natAbs → X → ℂ) {K : ℝ≥0}
    (hf₀ : LipschitzWith K f₀) (hf : ∀ j, LipschitzWith K (f j))
    (h₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hbound : ∀ j x, ‖f j x‖ ≤ 1) :
    LipschitzWith ((m.natAbs + 1 : ℝ≥0) * K)
      (fun x => f₀ x * star (signedTensorProduct m (fun j => f j x))) := by
  have h := lipschitz_mul_star_of_bounds f₀ (fun x => signedTensorProduct m (fun j => f j x))
    (Bf := 1) (Bg := 1) hf₀ (signedTensorProduct_lipschitz m f hf hbound)
    h₀ (fun x => signedTensorProduct_norm_le m _ (fun j => hbound j x))
  convert h using 1
  ring

namespace RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound)

theorem dilationObservable_lipschitz (q : ℚ)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
    (hEL : E.lattice = M.dilationPairLattice q)
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [T2Space (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hheight : ∀ j a k, rationalLogHeight
      (D.basis.repr (M.filtration.ordinary.dilationPairProjection q j (E.basis a)) k) ≤ p)
    (m : ℤ) (ε : D.RealGroup) (u₀ : D.Space → ℂ) (u : Fin m.natAbs → D.Space → ℂ)
    (K A : ℝ≥0) (h₀ : ∀ x, ‖u₀ x‖ ≤ 1) (hu : ∀ j x, ‖u j x‖ ≤ 1)
    (hLip₀ : letI := D.metricSpace; LipschitzWith K u₀)
    (hLip : letI := D.metricSpace; ∀ j, LipschitzWith K (u j))
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) :
    letI := E.metricSpace
    LipschitzWith ((m.natAbs + 1 : ℝ≥0) *
      (K * (A * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩)))
      (M.dilationObservable q E hEL m ε u₀ u) := by
  let := E.metricSpace
  let := D.metricSpace
  apply lipschitz_signed_tensor_cross_product m
    (fun x => u₀ (ε • M.dilationSpaceProjection q E hEL 0 x))
    (fun j x => u j (ε • M.dilationSpaceProjection q E hEL 1 x))
  · exact hLip₀.comp (hε.comp (M.dilationSpaceProjection_lipschitz q E hEL 0 hp hD hE (hheight 0)))
  · exact fun j => (hLip j).comp
      (hε.comp (M.dilationSpaceProjection_lipschitz q E hEL 1 hp hD hE (hheight 1)))
  · exact fun x => h₀ _
  · exact fun j x => hu j _

end RationalFilteredNilmanifold.MultidegreeStructure

end Erdos3

end

end OAI
