import OAI.Combinatorics.Progressions.Geometry.SquarefreeActionMetric

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))

noncomputable def nativeSpaceMap : D.Space → E.Space :=
  cosetMap D.realLattice E.realLattice
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ)
    (realificationMap_subgroup φ D.lattice E.lattice hφ)

theorem nativeSpaceMap_mk (x : D.RealGroup) :
    D.nativeSpaceMap E φ hφ (QuotientGroup.mk x) =
      QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ x) := rfl

theorem nativeSpaceMap_smul (z : D.RealGroup) (x : D.Space) :
    D.nativeSpaceMap E φ hφ (z • x) =
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ z • D.nativeSpaceMap E φ hφ x :=
  cosetMap_smul _ _ _ _ z x

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]

theorem nativeSpaceMap_lipschitz {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hentries : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) :
    letI := D.metricSpace
    letI := E.metricSpace
    LipschitzWith ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩ (D.nativeSpaceMap E φ hφ) := by
  let := D.metricSpace
  let := E.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  exact D.nativeMap_dist_le E φ hφ hp hD hE hentries u v

end Erdos3.RationalFilteredNilmanifold

end

end OAI
