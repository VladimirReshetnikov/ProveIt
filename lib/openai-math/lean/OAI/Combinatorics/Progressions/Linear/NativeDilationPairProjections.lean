/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.ControlledComparisonModel
import OAI.Combinatorics.Progressions.Estimates.RealifiedDilationMultidegree

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def dilationPairProjection (q : ℚ) (j : Fin 2) : F.dilationPairSubalgebra q →ₗ⁅ℚ⁆ L :=
  (liePiEval j).comp (F.dilationPairToPi q)

@[simp] theorem dilationPairProjection_zero (q : ℚ) :
    F.dilationPairProjection q 0 = F.dilationPairFirst q := rfl

@[simp] theorem dilationPairProjection_one (q : ℚ) :
    F.dilationPairProjection q 1 = F.dilationPairSecond q := rfl

noncomputable def realDilationPairProjection (q : ℚ) (j : Fin 2) :
    (F.dilationPairFiltration q).realification.Group →* F.realification.Group :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (F.dilationPairFiltration q).lowerCentralSeries_eq_bot)
    (hM := F.lowerCentralSeries_eq_bot) (F.dilationPairProjection q j)

theorem realifiedDilationPairEquiv_projection (q : ℚ) (j : Fin 2)
    (x : ℝ ⊗[ℚ] F.dilationPairSubalgebra q) :
    pairToPi (F.realifiedDilationPairEquiv q x).val j =
      realificationLieHom (F.dilationPairProjection q j) x := by
  rw [F.realifiedDilationPairEquiv_coe]
  induction x using TensorProduct.inductionOn with
  | tmul scalar vector =>
    rw [realificationLieHom_tmul, realPairEquiv_tmul, realificationLieHom_tmul]
    fin_cases j <;> rfl
  | add first second hfirst hsecond =>
    simp only [map_add, Pi.add_apply, hfirst, hsecond]

theorem realDilationPairProjection_coord (q : ℚ) (j : Fin 2)
    (g : (F.dilationPairFiltration q).realification.Group) :
    (F.realDilationPairProjection q j g).coord =
      pairToPi (F.realifiedDilationPairEquiv q g.coord).val j :=
  (F.realifiedDilationPairEquiv_projection q j g.coord).symm

theorem realDilationPairProjection_jointly_injective (q : ℚ)
    {g h : (F.dilationPairFiltration q).realification.Group}
    (heq : ∀ j, F.realDilationPairProjection q j g = F.realDilationPairProjection q j h) :
    g = h := by
  apply NilpotentLieBCHGroup.ext
  apply (F.realifiedDilationPairEquiv q).injective
  apply Subtype.ext
  apply pairToPi_injective
  funext j
  simpa only [F.realDilationPairProjection_coord] using
    congrArg NilpotentLieBCHGroup.coord (heq j)

theorem realDilationPairProjection_mem (q : ℚ) (j : Fin 2) {n : ℕ}
    {g : (F.dilationPairFiltration q).realification.Group}
    (hg : g ∈ (F.dilationPairFiltration q).realification.subgroup n) :
    F.realDilationPairProjection q j g ∈ F.realification.subgroup n := by
  have hm := (F.realifiedDilationPairEquiv_mem_layer q n g.coord).mp hg
  change (F.realDilationPairProjection q j g).coord ∈ F.realification.layer n
  rw [F.realDilationPairProjection_coord]
  fin_cases j
  · exact hm.1
  · exact hm.2.1

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem dilationPairProjection_lattice (q : ℚ) (j : Fin 2) :
    M.dilationPairLattice q ≤ D.lattice.comap
      (mapOfSteps (M.filtration.ordinary.dilationPairProjection q j)) := by
  intro x hx
  have h := (M.dilationPairLattice_mem q x).mp hx
  fin_cases j
  · exact h.1
  · exact h.2

noncomputable def dilationSpaceProjection (q : ℚ)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
    (hE : E.lattice = M.dilationPairLattice q) (j : Fin 2) : E.Space → D.Space :=
  cosetMap E.realLattice D.realLattice (M.filtration.ordinary.realDilationPairProjection q j)
    (realificationMap_subgroup (M.filtration.ordinary.dilationPairProjection q j) _ _
      (by rw [hE]; exact M.dilationPairProjection_lattice q j))

theorem dilationSpaceProjection_mk (q : ℚ)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
    (hE : E.lattice = M.dilationPairLattice q) (j : Fin 2) (g : E.RealGroup) :
    M.dilationSpaceProjection q E hE j (QuotientGroup.mk g) =
      QuotientGroup.mk (M.filtration.ordinary.realDilationPairProjection q j g) := rfl

theorem dilationSpaceProjection_smul (q : ℚ)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
    (hE : E.lattice = M.dilationPairLattice q) (j : Fin 2) (g : E.RealGroup) (x : E.Space) :
    M.dilationSpaceProjection q E hE j (g • x) =
      M.filtration.ordinary.realDilationPairProjection q j g •
        M.dilationSpaceProjection q E hE j x := cosetMap_smul _ _ _ _ _ _

theorem dilationSpaceProjection_lipschitz (q : ℚ)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
    (hEL : E.lattice = M.dilationPairLattice q) (j : Fin 2)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [T2Space (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hheight : ∀ a k, rationalLogHeight
      (D.basis.repr (M.filtration.ordinary.dilationPairProjection q j (E.basis a)) k) ≤ p) :
    letI := E.metricSpace
    letI := D.metricSpace
    LipschitzWith ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩
      (M.dilationSpaceProjection q E hEL j) := by
  let := E.metricSpace
  let := D.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact nativeMap_dist_le E D (M.filtration.ordinary.dilationPairProjection q j)
        (by rw [hEL]; exact M.dilationPairProjection_lattice q j)
        hp hE hD (fun k a => hheight a k) x y

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
