import OAI.Combinatorics.Progressions.Probability.DensityMixtureAELaw
import OAI.Combinatorics.Progressions.Probability.NormalizedJetDensitySupport

namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def splitFreeCoordinates (I J N : Type*) [Fintype I] [Fintype J] [Fintype N] :
    ((J ⊕ N → ℝ) × (I → ℝ)) ≃ᵐ (((J → ℝ) × (I → ℝ)) × (N → ℝ)) :=
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ N => ℝ)).prodCongr
    (MeasurableEquiv.refl (I → ℝ))).trans
    (MeasurableEquiv.prodAssoc.trans
      (((MeasurableEquiv.refl (J → ℝ)).prodCongr MeasurableEquiv.prodComm).trans
        MeasurableEquiv.prodAssoc.symm))

theorem splitFreeCoordinates_apply {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (p : (J ⊕ N → ℝ) × (I → ℝ)) :
    splitFreeCoordinates I J N p = (((fun j => p.1 (.inl j)), p.2), fun n => p.1 (.inr n)) := rfl

theorem splitFreeCoordinates_symm_apply {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (p : ((J → ℝ) × (I → ℝ)) × (N → ℝ)) :
    (splitFreeCoordinates I J N).symm p = (Sum.elim p.1.1 p.2, p.1.2) := rfl

theorem splitFreeCoordinates_preserving (I J N : Type*) [Fintype I] [Fintype J] [Fintype N] :
    MeasurePreserving (splitFreeCoordinates I J N) volume volume := by
  have h₁ := (volume_measurePreserving_sumPiEquivProdPi (fun _ : J ⊕ N => ℝ)).prod
    (MeasurePreserving.id (volume : Measure (I → ℝ)))
  have h₂ : MeasurePreserving
      (MeasurableEquiv.prodAssoc : ((J → ℝ) × (N → ℝ)) × (I → ℝ) ≃ᵐ _)
      volume volume := volume_preserving_prodAssoc
  have h₃ := (MeasurePreserving.id (volume : Measure (J → ℝ))).prod
    (Measure.measurePreserving_swap (μ := (volume : Measure (N → ℝ))) (ν := (volume : Measure (I → ℝ))))
  have h₄ : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm : (J → ℝ) × ((I → ℝ) × (N → ℝ)) ≃ᵐ _)
      volume volume := volume_preserving_prodAssoc.symm MeasurableEquiv.prodAssoc
  exact h₄.comp (h₃.comp (h₂.comp h₁))

theorem splitFreeProfile_measure {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (f : (J → ℝ) × (I → ℝ) → ℝ) (g : (N → ℝ) → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ p, 0 ≤ f p) :
    (realDensityMeasure volume (splitFreeProfile f g)).map (splitFreeCoordinates I J N) =
      (realDensityMeasure volume f).prod (realDensityMeasure volume g) := by
  rw [realDensityMeasure_map_equiv, (splitFreeCoordinates_preserving I J N).map_eq,
    binaryDensity_measure volume volume f g hf hg hf0]
  rfl

end Erdos3

end

end OAI
