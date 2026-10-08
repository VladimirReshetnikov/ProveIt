/- Modified for ProveIt: supply the proved Euclidean-layer measurable-open
instances explicitly in physicalRowsStandardEquiv on Lean 4.32. All upstream
declaration statements are unchanged. -/
import OAI.Combinatorics.Progressions.Geometry.PhysicalRowsStandardCoordinates

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped Classical

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})
local notation "Std" => (fun j : Fin m => BoundedBooleanJet (Fin q) (Fin.val j + 1))

noncomputable def physicalRowsStandardEquiv : EuclideanJetLayers U Row ≃ᵐ EuclideanJetLayers U Std where
  toFun := physicalRowsToStandard U
  invFun z j s := z j (boundedBooleanJetRowsEquiv (Fin q) (j.val + 1) s)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    let : OpensMeasurableSpace (EuclideanJetLayers U Row) :=
      @BorelSpace.opensMeasurable _ _ _ (euclideanJetLayers_borel U)
    exact (physicalRowsToStandard_continuous U).measurable
  measurable_invFun := by
    let : OpensMeasurableSpace (EuclideanJetLayers U Std) :=
      @BorelSpace.opensMeasurable _ _ _ (euclideanJetLayers_borel U)
    apply Continuous.measurable
    apply continuous_pi
    intro j
    apply continuous_pi
    intro s
    exact (continuous_apply (boundedBooleanJetRowsEquiv (Fin q) (j.val + 1) s)).comp (continuous_apply j)

variable [CompactSpace (CoefficientTorus (K := Fin q) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
variable [BorelSpace (CoefficientTorus (K := Fin q) U)]
variable (μ : Measure (CoefficientTorus (K := Fin q) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include μ in
theorem physicalRows_projected_density_law {K : Type*} [Fintype K]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (ρ : Measure (CoefficientTorus (K := K) U))
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (g : EuclideanJetLayers U Std → ℝ)
    (hlaw : ρ.map (euclideanCoefficientJetMap U root D
      (fun j => (Subtype.val : Std j → Finset (Fin q)))) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : Std j => ν j))) g) :
    ρ.map (euclideanCoefficientJetMap U root D (fun j => (Subtype.val : Row j → Finset (Fin q)))) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : Row j => ν j)))
        (fun z => g (physicalRowsToStandard U z)) := by
  let e := physicalRowsStandardEquiv (q := q) U
  have hp : MeasurePreserving e
      (Measure.pi (fun j => Measure.pi (fun _ : Row j => ν j)))
      (Measure.pi (fun j => Measure.pi (fun _ : Std j => ν j))) :=
    physicalRowsToStandard_measurePreserving U μ ν
  have hi := MeasurePreserving.symm e hp
  have hh := congrArg (Measure.map e.symm) hlaw
  rw [Measure.map_map e.symm.measurable
    (euclideanCoefficientJetMap_continuous U root D _).measurable,
    realDensityMeasure_map_equiv, hi.map_eq] at hh
  have he : e.symm ∘ euclideanCoefficientJetMap U root D
      (fun j => (Subtype.val : Std j → Finset (Fin q))) =
      euclideanCoefficientJetMap U root D (fun j => (Subtype.val : Row j → Finset (Fin q))) := by
    funext z
    apply e.injective
    change e (e.symm _) = _
    rw [e.apply_symm_apply]
    exact (physicalRowsToStandard_coefficient U root D z).symm
  rw [he] at hh
  convert hh using 1
  congr! (transparency := .reducible)

end Erdos3.BooleanCubeKernel

end

end OAI
