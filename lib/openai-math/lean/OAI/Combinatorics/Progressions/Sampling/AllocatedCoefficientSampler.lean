import OAI.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedCoefficientDensity :
    CoefficientTorus (K := LayerSamplerVariables G I n B) U → ℝ :=
  canonicalCoefficientDensity U b hb o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (allocatedLayerIntegerPMFs B U b hR hσ S)

noncomputable def allocatedCoefficientSource :
    Measure (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :=
  Measure.pi (fun j => mixedScalarArrayLaw (allocatedLayerCenters B U b S j)
    (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j))

theorem allocatedCoefficientSource_probability :
    IsProbabilityMeasure (allocatedCoefficientSource B U b hR hσ S) := by
  let : ∀ j, IsProbabilityMeasure (mixedScalarArrayLaw (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j)) :=
    fun j => mixedScalarArrayLaw_probability _ _ (allocatedLayerWidths_pos B U b hR hσ S j) _
  exact Measure.pi.instIsProbabilityMeasure _

variable (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)

include hσ1 C hC hchart hsmall in
theorem allocatedCoefficientDensity_recover
    {y : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    (hy : allocatedCoefficientDensity B U b hb o hR hσ S y ≠ 0) :
    ∃! a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n,
      (canonicalCoefficientSample U b hb o a = y ∧
        ∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (a j) ∧
          mixedArraySupported (allocatedLayerCenters B U b S j) (allocatedLayerWidths B U b S j)
            (allocatedLayerIntegerPMFs B U b hR hσ S j) (a j)) ∧
      ∀ j x, (∀ v, |x v| ≤ layerSamplerBox B U b S v) →
        mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val (a j).1 (a j).2 x ∈
          standardLatticeSmallBox (J j) := by
  obtain ⟨a, ha, hu⟩ := canonicalCoefficientDensity_recover_unique U b hb o
    (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (allocatedLayerIntegerPMFs B U b hR hσ S) hy
  refine ⟨a, ⟨ha, ?_⟩, fun z hz => hu z hz.1⟩
  intro j x hx
  exact allocatedLayerSupported_polynomial_chart B U b hR hσ S o hσ1 C hC hchart hsmall
    j (a j) (ha.2 j).2 x hx

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include hσ1 C hC hchart hsmall ν

theorem allocatedCoefficientDensity_spec :
    Measurable (allocatedCoefficientDensity B U b hb o hR hσ S) ∧
      (∀ y, 0 ≤ allocatedCoefficientDensity B U b hb o hR hσ S y) ∧
      Integrable (allocatedCoefficientDensity B U b hb o hR hσ S) μ ∧
      (∫ y, allocatedCoefficientDensity B U b hb o hR hσ S y ∂μ) = 1 ∧
      Measure.map (canonicalCoefficientSample U b hb o) (allocatedCoefficientSource B U b hR hσ S) =
        realDensityMeasure μ (allocatedCoefficientDensity B U b hb o hR hσ S) := by
  have hw := allocatedLayerWidths_pos B U b hR hσ S
  have hs := allocatedLayerColumns_chart B U b hR hσ S o hσ1 C hC hchart hsmall
  have hm := canonicalCoefficientDensity_mass U b hb o (allocatedLayerCenters B U b S)
    (allocatedLayerWidths B U b S) (allocatedLayerIntegerPMFs B U b hR hσ S) μ ν hw hs
  exact ⟨canonicalCoefficientDensity_measurable U b hb o _ _ _,
    canonicalCoefficientDensity_nonneg U b hb o _ _ _ hw, hm.1, hm.2,
    canonicalCoefficientDensity_law U b hb o _ _ _ μ ν hw hs⟩

theorem exists_allocatedCoefficientSampler (L₀ : ℕ) :
    ∃ S : LayerSamplerScale (G := G) B U b R σ,
      L₀ ≤ S.value ∧ S.value ≤ layerSamplerScaleBound (G := G) B R σ L₀ ∧
      IsProbabilityMeasure (allocatedCoefficientSource B U b hR hσ S) ∧
      Measurable (allocatedCoefficientDensity B U b hb o hR hσ S) ∧
      (∀ y, 0 ≤ allocatedCoefficientDensity B U b hb o hR hσ S y) ∧
      Integrable (allocatedCoefficientDensity B U b hb o hR hσ S) μ ∧
      (∫ y, allocatedCoefficientDensity B U b hb o hR hσ S y ∂μ) = 1 ∧
      Measure.map (canonicalCoefficientSample U b hb o) (allocatedCoefficientSource B U b hR hσ S) =
        realDensityMeasure μ (allocatedCoefficientDensity B U b hb o hR hσ S) ∧
      ∀ y, allocatedCoefficientDensity B U b hb o hR hσ S y ≠ 0 →
        ∃! a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n,
          (canonicalCoefficientSample U b hb o a = y ∧
            ∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (a j) ∧
              mixedArraySupported (allocatedLayerCenters B U b S j) (allocatedLayerWidths B U b S j)
                (allocatedLayerIntegerPMFs B U b hR hσ S j) (a j)) ∧
          ∀ j x, (∀ v, |x v| ≤ layerSamplerBox B U b S v) →
            mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val (a j).1 (a j).2 x ∈
              standardLatticeSmallBox (J j) := by
  obtain ⟨S, hlo, hhi⟩ := exists_layerSamplerScale (G := G) B U b R σ hR hσ L₀
  have hs := allocatedCoefficientDensity_spec B U b hb o hR hσ S hσ1 C hC hchart hsmall μ ν
  exact ⟨S, hlo, hhi, allocatedCoefficientSource_probability B U b hR hσ S,
    hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2,
    fun _ hy => allocatedCoefficientDensity_recover B U b hb o hR hσ S hσ1 C hC hchart hsmall hy⟩

end Erdos3.VectorPolynomial

end

end OAI
