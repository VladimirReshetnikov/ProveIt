import OAI.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Classical

theorem centeredFinite_spatial_modular_good_set
    {C Ω G P : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {n : ℕ}
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    (noise : Ω → (Option (G ⊕ P) × Fin n → ℤ))
    (V : Option (G ⊕ P) × Fin n → ℝ)
    (e : Fin 2 × Fin n ↪ G) (κ : ℝ)
    (modularBad : Set (C × Ω)) (hmeas : MeasurableSet modularBad)
    {εmod εsp : ℝ}
    (hmodmass : (centeredFiniteProbabilityMeasure μ law).real modularBad ≤ εmod)
    (hspmass : (centeredFiniteProbabilityMeasure μ law).real
      {z | spatialMatrixBlockBad e V (κ / 2) (noise z.2)} ≤ εsp)
    (charge : C × Ω → ℕ) (cutoff : ℕ)
    (hmodular : ∀ c x, 0 < (law c).weight x →
      ((c, x) ∈ modularBad ↔ cutoff < charge (c, x)))
    (recovered : C × Ω → Prop)
    (hae : ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, recovered z) :
    let bad := modularBad ∪ {z | spatialMatrixBlockBad e V (κ / 2) (noise z.2)}
    MeasurableSet bad ∧
      (centeredFiniteProbabilityMeasure μ law).real bad ≤ εmod + εsp ∧
      ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law,
        z ∉ bad → recovered z ∧ charge z ≤ cutoff ∧
          ∀ block : Fin 2, κ / 2 < |Matrix.det (fun i j : Fin n =>
            spatialMatrixNormalizedEntries e V (noise z.2) (block, j, i))| := by
  have hspmeas : MeasurableSet
      {z : C × Ω | spatialMatrixBlockBad e V (κ / 2) (noise z.2)} :=
    (Set.toFinite {x : Ω | spatialMatrixBlockBad e V (κ / 2) (noise x)}).measurableSet.preimage
      measurable_snd
  refine ⟨hmeas.union hspmeas, ?_, ?_⟩
  · exact (measureReal_union_le _ _).trans (add_le_add hmodmass hspmass)
  · filter_upwards [centeredFiniteProbabilityMeasure_ae_positive_weight μ law hweight, hae]
      with z hz hrec
    intro hgood
    have hmod : z ∉ modularBad := fun h => hgood (Or.inl h)
    have hsp : ¬spatialMatrixBlockBad e V (κ / 2) (noise z.2) :=
      fun h => hgood (Or.inr h)
    refine ⟨hrec, le_of_not_gt (fun h => hmod ((hmodular z.1 z.2 hz).mpr h)), ?_⟩
    intro block
    exact lt_of_not_ge (fun h => hsp ⟨block, h⟩)

end Erdos3

end

end OAI
