import OAI.Combinatorics.Progressions.Estimates.EuclideanGraphNorm
import OAI.Combinatorics.Progressions.Estimates.EuclideanGraphResidual

namespace OAI

section

namespace Erdos3

theorem euclidean_shift_subspace_surjective
    {σ κ : Type*} [Fintype σ] [Fintype κ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (hproj : Z.map ((LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp
      productEuclideanEquiv.symm.toLinearMap) = ⊤) :
    Function.Surjective ((euclideanDerivativeShiftMap T hT).comp Z.subtype) := by
  have hmap : Z.map (euclideanDerivativeShiftMap T hT) = ⊤ := by
    change Z.map ((coordinateScaleEquiv T hT).toLinearMap.comp
      ((LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp productEuclideanEquiv.symm.toLinearMap)) = ⊤
    rw [Submodule.map_comp, hproj, Submodule.map_top]
    exact (coordinateScaleEquiv T hT).range
  intro x
  have hx : x ∈ Z.map (euclideanDerivativeShiftMap T hT) := by rw [hmap]; trivial
  obtain ⟨v, hv, he⟩ := hx
  exact ⟨⟨v, hv⟩, he⟩

theorem exists_euclidean_lattice_graph_identity
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (Λ : Submodule ℤ Z) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (hinteger : ∀ x ∈ Λ,
      euclideanDerivativeShiftMap T (fun i => (hT i).ne') x.val ∈ realIntegerGrid)
    (hsurj : Function.Surjective
      ((euclideanDerivativeShiftMap T (fun i => (hT i).ne')).comp Z.subtype)) :
    let π : Z →ₗ[ℝ] (σ → ℝ) :=
      (euclideanDerivativeShiftMap T (fun i => (hT i).ne')).comp Z.subtype
    ∃ G : (σ → ℝ) →ₗ[ℝ] Z,
      (∀ y i, (G y).val (Sum.inl i) = y i) ∧
      (∀ x : Z, G (fun i => x.val (Sum.inl i)) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume Λ = ZLattice.covolume (latticeKernel Λ π)
        (MeasureTheory.volume (α := LinearMap.ker π)) *
        (((latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup : ℝ) /
          ∏ i, T i) *
        Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det := by
  let π := (euclideanDerivativeShiftMap T (fun i => (hT i).ne')).comp Z.subtype
  obtain ⟨G, hright, hsection, hcov⟩ :=
    exists_scaled_lattice_covolume_identity Λ π hinteger hsurj T hT
  refine ⟨G, ?_, ?_, hcov⟩
  · intro y i
    have he := congrFun (hright y) i
    change T i * (G y).val (Sum.inl i) = T i * y i at he
    exact mul_left_cancel₀ (hT i).ne' he
  · intro x
    have he : (fun i => π x i / T i) = fun i => x.val (Sum.inl i) := by
      funext i
      exact mul_div_cancel_left₀ _ (hT i).ne'
    simpa only [he] using hsection x

end Erdos3

end

end OAI
