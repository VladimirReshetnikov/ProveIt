import OAI.Combinatorics.Progressions.Lattices.SelectedResidueCenterMix
import OAI.Combinatorics.Progressions.Probability.TranslatedSelectedOneSiteLaw

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

theorem exists_mixed_center_selected_sampler_oneSite_law (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ)+1) * R j ≤ 1/4)
    (L₀ : ℕ) {P δ : ℝ} (_hP : 0 ≤ P) (_hδ : 0 < δ) (_hδsmall : δ ≤ 1/6)
    (_hδP : δ⁻¹ ≤ Real.exp P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (root : LayerSamplerVariables G I n B → ℤ) (_hroot : ∀ k, |(root k : ℝ)| ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S ρ : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (_hρ : 0 < ρ) (_hρP : 1/ρ ≤ Real.exp P)
    (H : X → ℝ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ H k)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) H Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (W : Option (LayerSamplerVariables G I n B) × X → ℝ) (hW : ∀ z, 0 < W z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ W z),
    let D := fun center => translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀
      (coefficientConstantCenter U center) p hm
    let Z := fun center => selectedResidueDensityMass stride T W (D center)
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : ∀ center, 0 < Z center,
      (∀ center, |Z center-1| ≤ 3*δ ∧ 1/2 ≤ Z center ∧ Z center ≤ 3/2) ∧
      ∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
        ‖(∫ center, ∑' z, ((selectedResidueDensityPMF stride T W hW hZ (D center)
          (translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
            (coefficientConstantCenter U center) p hm) (hD center) z).toReal : ℂ) *
            φ (physicalAffineSite root z) ∂μ) -
          (∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
            φ (physicalAffineSite root z))‖ ≤ 6*δ := by
  obtain ⟨A, hA, hlaw⟩ := exists_translated_selected_sampler_oneSite_law m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP root hroot p hp hm stride hs Rrank S ρ
    hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth
  obtain ⟨hZ, hcenters⟩ := hlaw B U b hb o μ ν R σ hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall L₀ hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP
    root hroot p hp hm stride hs hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth
  choose hD hrest using (fun center : CoefficientTorus (K := LayerSamplerVariables G I n B) U =>
    hcenters (coefficientConstantCenter U center))
  refine ⟨hZ, hD, ?_, ?_⟩
  · intro center
    exact ⟨(hrest center).1, (hrest center).2.1, (hrest center).2.2.1⟩
  · intro φ hφ
    let D₀ := VectorPolynomial.selectedCoefficientDensity (G := G) B U b hb o R σ hR hσ L₀
    have hD₀ := selectedCoefficientDensity_measurable (G := G) B U b hb o R σ hR hσ L₀
    obtain ⟨M, hM⟩ := selectedCoefficientDensity_bounded (G := G) B U b hb o R σ hR hσ L₀
      C V hC hV hσ1 Cinv hCinv hchart hsmall
    have hbound (x) : ‖D₀ x‖ ≤ M := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hM x).1]
      exact (hM x).2
    let scale := selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀
    have hspec := allocatedCoefficientDensity_spec B U b hb o hR hσ scale
      hσ1 Cinv hCinv hchart hsmall μ ν
    let D := fun center => translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀
      (coefficientConstantCenter U center) p hm
    let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      affineSampleCoefficientTorus U p hm (fun k j => (z (k,j) : ℝ))
    let F := fun center z => coefficientFiberAverage U μ root
      (fun x => D₀ (coefficientConstantCenter U center+x))
      (coefficientEvaluationTorus U root (sample z))
    apply selectedResidue_center_mixture_compare μ stride T W hW hZ D
      (fun z => (translatedSelectedPhysicalDensity_measurable_center B U b hb o R σ hR hσ L₀ p hm z).comp
        (coefficientConstantCenter_continuous U).measurable)
      (fun center => translatedSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀
        (coefficientConstantCenter U center) p hm) hD F
      (fun z => coefficientMixedFiber_integrable U μ D₀ hD₀ hbound root _)
      (fun z => (coefficientMixedFiber_average U μ D₀ hD₀ hbound root _).trans hspec.2.2.2.1)
      (fun z => φ (physicalAffineSite root z)) (fun z => hφ _)
    intro center
    exact (hrest center).2.2.2 φ hφ

end Erdos3.BooleanCubeKernel

end

end OAI
