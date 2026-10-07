import OAI.Combinatorics.Progressions.Estimates.CoefficientProductHaar
import OAI.Combinatorics.Progressions.Geometry.CoefficientCoordinateEquiv

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

abbrev EuclideanCoefficientLayers :=
  ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) →
    euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup

instance euclideanCoefficientLayers_borel [Fintype K] :
    BorelSpace (EuclideanCoefficientLayers (K := K) U) := by
  let : ∀ j, BorelSpace (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun _ => QuotientAddGroup.borelSpace
  let : ∀ j, BorelSpace (BoundedCoefficientExponent K (j.val + 1) → euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun _ => Pi.borelSpace
  exact Pi.borelSpace

noncomputable def euclideanCoefficientEquiv :
    CoefficientTorus (K := K) U ≃+ EuclideanCoefficientLayers (K := K) U where
  toFun x j d := (euclideanSubspaceTorusEquiv (U j)).symm
    (coefficientCoordinateEquiv U x ⟨j, d⟩)
  invFun y := (coefficientCoordinateEquiv U).symm
    (fun s => euclideanSubspaceTorusEquiv (U s.1) (y s.1 s.2))
  left_inv x := by
    apply (coefficientCoordinateEquiv U).injective
    rw [AddEquiv.apply_symm_apply]
    funext s
    exact (euclideanSubspaceTorusEquiv (U s.1)).apply_symm_apply _
  right_inv y := by
    funext j d
    dsimp only
    rw [AddEquiv.apply_symm_apply]
    exact (euclideanSubspaceTorusEquiv (U j)).symm_apply_apply _
  map_add' x y := by
    funext j d
    simp only [map_add, Pi.add_apply]

theorem euclideanCoefficientEquiv_apply (x : CoefficientTorus (K := K) U)
    (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1)) :
    euclideanCoefficientEquiv U x j d = (euclideanSubspaceTorusEquiv (U j)).symm
      (coefficientCoordinateTorus U x ⟨j, d⟩) := rfl

theorem euclideanCoefficientEquiv_continuous [Fintype K] :
    Continuous (euclideanCoefficientEquiv (K := K) U) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro d
  exact (euclideanSubspaceTorusEquiv_symm_continuous (U j)).comp
    ((continuous_apply ⟨j, d⟩).comp (coefficientCoordinateTorus_continuous U))

noncomputable def euclideanCoefficientHomeomorph [Fintype K]
    [CompactSpace (CoefficientTorus (K := K) U)] :
    CoefficientTorus (K := K) U ≃ₜ EuclideanCoefficientLayers (K := K) U := by
  exact Continuous.homeoOfEquivCompactToT2
    (f := (euclideanCoefficientEquiv U).toEquiv) (euclideanCoefficientEquiv_continuous U)

noncomputable def euclideanCoefficientMeasurableEquiv [Fintype K]
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)] :
    CoefficientTorus (K := K) U ≃ᵐ EuclideanCoefficientLayers (K := K) U :=
  (euclideanCoefficientHomeomorph U).toMeasurableEquiv

theorem euclideanCoefficient_measurePreserving [Fintype K]
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)] :
    MeasurePreserving (euclideanCoefficientEquiv U) μ
      (Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j))) := by
  let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j))
  let : CompactSpace (EuclideanCoefficientLayers (K := K) U) := by
    have hc := isCompact_univ.image (euclideanCoefficientEquiv_continuous (K := K) U)
    rw [Set.image_univ, Set.range_eq_univ.mpr (euclideanCoefficientEquiv U).surjective] at hc
    exact ⟨hc⟩
  let : ∀ j, IsProbabilityMeasure
      (Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j)) :=
    fun j => Measure.pi.instIsProbabilityMeasure _
  let : IsProbabilityMeasure ξ := Measure.pi.instIsProbabilityMeasure _
  let : IsFiniteMeasure ξ := ⟨by simp [measure_univ]⟩
  let : ∀ j, (Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j)).IsAddLeftInvariant :=
    fun j => Measure.pi.isAddLeftInvariant _
  let : ξ.IsAddLeftInvariant := Measure.pi.isAddLeftInvariant _
  let : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  let : ξ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := ⟨fun _ _ => measure_lt_top ξ _⟩
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := ξ) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving
    (f := (euclideanCoefficientEquiv U).toAddMonoidHom)
    (euclideanCoefficientEquiv_continuous U) (euclideanCoefficientEquiv U).surjective (by simp)

end Erdos3.VectorPolynomial

end

end OAI
