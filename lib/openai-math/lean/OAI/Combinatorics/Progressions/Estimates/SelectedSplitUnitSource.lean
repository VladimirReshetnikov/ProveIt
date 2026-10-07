import OAI.Combinatorics.Progressions.Lattices.JointAffineL1Parameter

namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def selectedSplitMeasurableEquiv {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J) :
    ((UnselectedColumn s ⊕ N → ℝ) × (I → ℝ)) ≃ᵐ (J ⊕ N → ℝ) :=
  (splitFreeCoordinates I (UnselectedColumn s) N).trans
    (((selectedCoefficientMeasurableEquiv s).prodCongr (MeasurableEquiv.refl (N → ℝ))).trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ N => ℝ)).symm)

theorem selectedSplitMeasurableEquiv_apply {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J)
    (p : (UnselectedColumn s ⊕ N → ℝ) × (I → ℝ)) :
    selectedSplitMeasurableEquiv s p = selectedSplitCoefficients s p := rfl

theorem selectedSplitMeasurableEquiv_symm_apply {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J) (r : J ⊕ N → ℝ) :
    (selectedSplitMeasurableEquiv s).symm r =
      (Sum.elim (fun j : UnselectedColumn s => r (.inl j.val)) (fun n => r (.inr n)),
        fun i => r (.inl (s i))) := rfl

theorem measurableEquiv_inverse_law {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (ν : Measure Y) (he : μ.map e = ν) :
    ν.map e.symm = μ := by
  rw [← he, Measure.map_map e.symm.measurable e.measurable]
  simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply, Measure.map_id']

theorem affineProductProfile_map_law {I Y : Type*} [Fintype I] [MeasurableSpace Y]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (F : (I → ℝ) → Y) (hF : Measurable F) :
    (realDensityMeasure volume (smoothProductProfile I)).map
      (fun r => F (fun i => c i+w i*r i)) =
      (realDensityMeasure volume (affineProductProfile c w)).map F := by
  have hm : Measurable (fun r : I → ℝ => fun i => c i+w i*r i) := by fun_prop
  change Measure.map (F ∘ (fun (r : I → ℝ) i => c i+w i*r i)) _ = _
  rw [← Measure.map_map hF hm, affineProductProfile_law c w hw]

theorem selectedSplit_affine_law {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) :
    (realDensityMeasure volume (affineSelectedJetProfile s c w)).map
      (selectedSplitMeasurableEquiv s) = realDensityMeasure volume (affineProductProfile c w) := by
  have hf := selectedSplitCoefficients_law s
    (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j)))
    (affineProductProfile (fun n => c (.inr n)) (fun n => w (.inr n)))
    (affineProductProfile_contDiff _ _).continuous.measurable
    (affineProductProfile_contDiff _ _).continuous.measurable
    (affineProductProfile_integrable _ _ (fun j => hw (.inl j)))
    (affineProductProfile_integrable _ _ (fun n => hw (.inr n)))
    (affineProductProfile_nonneg _ _ (fun j => hw (.inl j)))
    (affineProductProfile_nonneg _ _ (fun n => hw (.inr n)))
  change (realDensityMeasure volume (affineSelectedJetProfile s c w)).map
    (selectedSplitMeasurableEquiv s) = _ at hf
  rw [← affineProductProfile_joined] at hf
  exact hf

theorem selectedSplit_unit_law {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) :
    (realDensityMeasure volume (smoothProductProfile (J ⊕ N))).map
      (fun r => (selectedSplitMeasurableEquiv s).symm (fun j => c j+w j*r j)) =
      realDensityMeasure volume (affineSelectedJetProfile s c w) := by
  exact (affineProductProfile_map_law c w hw _ (selectedSplitMeasurableEquiv s).symm.measurable).trans
    (measurableEquiv_inverse_law (selectedSplitMeasurableEquiv s) _ _ (selectedSplit_affine_law s c w hw))

end Erdos3

end

end OAI
