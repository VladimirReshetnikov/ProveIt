import OAI.Combinatorics.Progressions.Estimates.NativePhysicalHaarExpansion

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped Classical

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})

noncomputable def physicalRowsToStandard
    (z : EuclideanJetLayers U Row) :
    EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) :=
  fun j s => z j ((boundedBooleanJetRowsEquiv (Fin q) (j.val + 1)).symm s)

theorem physicalRowsToStandard_continuous :
    Continuous (physicalRowsToStandard (q := q) U) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro s
  exact (continuous_apply _).comp (continuous_apply j)

theorem physicalRowsToStandard_coefficient {K : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (z : CoefficientTorus (K := K) U) :
    physicalRowsToStandard U
      (euclideanCoefficientJetMap U root D (fun j => (Subtype.val : Row j → Finset (Fin q))) z) =
    euclideanCoefficientJetMap U root D
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))) z := by
  funext j s
  unfold physicalRowsToStandard
  simp only [euclideanCoefficientJetMap_apply]
  rfl

theorem physicalRowsToStandard_sample {X : Type*}
    (d : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin q) → ℤ) :
    physicalRowsToStandard U (physicalCubeRowSample U d (fun j => (Subtype.val : Row j → Finset (Fin q))) p hm v) =
      physicalCubeEuclideanSample U d p hm v := by
  rw [← coefficientCoverSample_physicalRows U d p hp hm, physicalRowsToStandard_coefficient]
  exact (physicalCubeEuclideanSample_frame U d p hp hm v).symm

variable [CompactSpace (CoefficientTorus (K := Fin q) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
variable [BorelSpace (CoefficientTorus (K := Fin q) U)]
variable (μ : Measure (CoefficientTorus (K := Fin q) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include μ in
theorem physicalRowsToStandard_measurePreserving :
    MeasurePreserving (physicalRowsToStandard (q := q) U)
      (Measure.pi (fun j => Measure.pi (fun _ : Row j => ν j)))
      (Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))) := by
  have hr := physicalRowsCoefficient_measurePreserving U μ ν 1 zero_lt_one
  have hs := standardPhysicalJetMap_measurePreserving U μ ν
  have hc := (physicalRowsToStandard_continuous (q := q) U).measurable
  refine ⟨hc, ?_⟩
  rw [← hr.map_eq, Measure.map_map hc hr.measurable]
  have he : (physicalRowsToStandard U ∘ (fun z =>
      euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ)
        (fun j => (Subtype.val : Row j → Finset (Fin q)))
        (quotientIntegerCover (coefficientIntegerLattice U) 1 z))) = standardPhysicalJetMap U := by
    funext z
    simp only [Function.comp_apply, physicalRowsToStandard_coefficient]
    congr 1
    change (1 : ℕ) • z = z
    exact one_nsmul z
  rw [he]
  exact hs.map_eq

end Erdos3.BooleanCubeKernel

end

end OAI
