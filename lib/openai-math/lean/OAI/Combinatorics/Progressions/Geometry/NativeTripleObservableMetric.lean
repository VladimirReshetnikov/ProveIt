import OAI.Combinatorics.Progressions.Estimates.NativeDilationDescent

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitz_three_conjugates_of_bounds {X : Type*} [PseudoMetricSpace X]
    (f : Fin 3 → X → ℂ) {K : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j))
    (hbound : ∀ j x, ‖f j x‖ ≤ 1) :
    LipschitzWith (3 * K) (fun x => f 0 x * star (f 1 x) * star (f 2 x)) := by
  have h01 := lipschitz_mul_star_of_bounds (f 0) (f 1)
    (Bf := 1) (Bg := 1) (hf 0) (hf 1) (hbound 0) (hbound 1)
  have hb01 (x : X) : ‖f 0 x * star (f 1 x)‖ ≤ 1 := by
    simpa only [norm_mul, norm_star, mul_one] using
      mul_le_mul (hbound 0 x) (hbound 1 x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h := lipschitz_mul_star_of_bounds (fun x => f 0 x * star (f 1 x)) (f 2)
    (Bf := 1) (Bg := 1) h01 (hf 2) hb01 (hbound 2)
  convert h using 1
  ring

namespace RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound)

theorem tripleObservable_lipschitz (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi c hc) s r)
    (hEL : E.lattice = M.additiveTripleLattice i hi c hc)
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [T2Space (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hheight : ∀ j a k, rationalLogHeight
      (D.basis.repr (M.filtration.additiveTripleProjection i hi c hc j (E.basis a)) k) ≤ p)
    (ε : D.RealGroup) (u : Fin 3 → D.Space → ℂ) (K A : ℝ≥0)
    (hu : ∀ j x, ‖u j x‖ ≤ 1)
    (hLip : letI := D.metricSpace; ∀ j, LipschitzWith K (u j))
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) :
    letI := E.metricSpace
    LipschitzWith (3 * (K * (A * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩)))
      (M.tripleObservable i hi c hc E hEL ε u) := by
  let := E.metricSpace
  let := D.metricSpace
  apply lipschitz_three_conjugates_of_bounds
    (fun j x => u j (ε • M.tripleSpaceProjection i hi c hc E hEL j x))
  · intro j
    exact (hLip j).comp (hε.comp
      (M.tripleSpaceProjection_lipschitz i hi c hc E hEL j hp hD hE (hheight j)))
  · exact fun j x => hu j _

end RationalFilteredNilmanifold.MultidegreeStructure
end Erdos3

end

end OAI
