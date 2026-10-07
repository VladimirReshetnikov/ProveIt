import OAI.Combinatorics.Progressions.Estimates.CommonRefilteredFactorization

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem additiveTripleProjection_lattice (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3) :
    M.additiveTripleLattice i hi c hc ≤ D.lattice.comap
      (mapOfSteps (M.filtration.additiveTripleProjection i hi c hc j)) := by
  intro x hx
  have h := (M.additiveTripleLattice_mem i hi c hc x).mp hx
  fin_cases j
  · exact h.1
  · exact h.2.1
  · exact h.2.2

noncomputable def tripleSpaceProjection (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi c hc) s r)
    (hE : E.lattice = M.additiveTripleLattice i hi c hc) (j : Fin 3) : E.Space → D.Space :=
  cosetMap E.realLattice D.realLattice (M.filtration.realAdditiveTripleProjection i hi c hc j)
    (realificationMap_subgroup (M.filtration.additiveTripleProjection i hi c hc j) _ _
      (by rw [hE]; exact M.additiveTripleProjection_lattice i hi c hc j))

theorem tripleSpaceProjection_mk (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi c hc) s r)
    (hE : E.lattice = M.additiveTripleLattice i hi c hc) (j : Fin 3) (g : E.RealGroup) :
    M.tripleSpaceProjection i hi c hc E hE j (QuotientGroup.mk g) =
      QuotientGroup.mk (M.filtration.realAdditiveTripleProjection i hi c hc j g) := rfl

theorem tripleSpaceProjection_smul (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi c hc) s r)
    (hE : E.lattice = M.additiveTripleLattice i hi c hc) (j : Fin 3)
    (g : E.RealGroup) (x : E.Space) :
    M.tripleSpaceProjection i hi c hc E hE j (g • x) =
      M.filtration.realAdditiveTripleProjection i hi c hc j g •
        M.tripleSpaceProjection i hi c hc E hE j x := cosetMap_smul _ _ _ _ _ _

theorem tripleSpaceProjection_lipschitz (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi c hc) s r)
    (hEL : E.lattice = M.additiveTripleLattice i hi c hc) (j : Fin 3)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [T2Space (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hheight : ∀ a k, rationalLogHeight
      (D.basis.repr (M.filtration.additiveTripleProjection i hi c hc j (E.basis a)) k) ≤ p) :
    letI := E.metricSpace
    letI := D.metricSpace
    LipschitzWith ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩
      (M.tripleSpaceProjection i hi c hc E hEL j) := by
  let := E.metricSpace
  let := D.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact nativeMap_dist_le E D (M.filtration.additiveTripleProjection i hi c hc j)
        (by rw [hEL]; exact M.additiveTripleProjection_lattice i hi c hc j)
        hp hE hD (fun k a => hheight a k) x y

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
