import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import OAI.Combinatorics.Progressions.Fourier.EuclideanJetTorus

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

theorem coefficientCoordinateTorus_measurePreserving {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ s : CoefficientSlot K m, MeasurableSpace (SubspaceArrayTorus Unit (U s.1))]
    [∀ s : CoefficientSlot K m, BorelSpace (SubspaceArrayTorus Unit (U s.1))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)] :
    MeasurePreserving (coefficientCoordinateTorus U) μ (Measure.pi ν) := by
  let _ := coefficientCoordinateTori_compact (K := K) U
  let _ : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  let _ : (Measure.pi ν).IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := Measure.pi ν) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving (coefficientCoordinateTorus_continuous U)
    (coefficientCoordinateTorus_surjective U) (by simp)

end Erdos3.VectorPolynomial

end

end OAI
