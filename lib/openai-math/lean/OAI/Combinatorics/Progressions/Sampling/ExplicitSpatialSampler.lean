import OAI.Combinatorics.Progressions.Estimates.AnchoredReferenceDomination
import OAI.Combinatorics.Progressions.Polynomial.PolynomialOneSiteComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)

theorem selectedCoefficientDensity_measurable
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] :
    Measurable (selectedCoefficientDensity (G := G) B U b hb o R σ hR hσ L₀) := by
  exact canonicalCoefficientDensity_measurable U b hb o _ _ _

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem selectedCoefficientDensity_bounded (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ)+1) * R j ≤ 1/4) :
    ∃ M : ℝ, ∀ x, 0 ≤ selectedCoefficientDensity (G := G) B U b hb o R σ hR hσ L₀ x ∧
      selectedCoefficientDensity (G := G) B U b hb o R σ hR hσ L₀ x ≤ M := by
  let S := selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀
  refine ⟨(allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ)^
    Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m), ?_⟩
  intro x
  have h := (allocatedCoefficientAmbientDensity_bounds B U b o S C V hC hV hR hσ).1
    (coefficientAmbientTorus U x)
  rw [allocatedCoefficientAmbientDensity_eq B U b hb o S hR hσ hσ1 Cinv hCinv hchart hsmall] at h
  exact h

include hC hV in
theorem selectedCoefficientDensity_fiber_integrable (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ)+1) * R j ≤ 1/4)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U)) [IsFiniteMeasure μ]
    (t : LayerSamplerVariables G I n B → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => selectedCoefficientDensity B U b hb o R σ hR hσ L₀
      (coefficientFiberMap U t y x)) μ := by
  obtain ⟨M, hM⟩ := selectedCoefficientDensity_bounded (G := G) B U b hb o R σ hR hσ L₀
    C V hC hV hσ1 Cinv hCinv hchart hsmall
  have hm := selectedCoefficientDensity_measurable (G := G) B U b hb o R σ hR hσ L₀
  apply Integrable.of_bound (hm.comp (coefficientFiberMap_continuous U t y).measurable).aestronglyMeasurable M
  exact ae_of_all μ (fun x => by
    dsimp only [Function.comp_def]
    rw [Real.norm_eq_abs, abs_of_nonneg (hM _).1]
    exact (hM _).2)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

theorem exists_selected_sampler_oneSite_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ)+1) * R j ≤ 1/4)
    (L₀ : ℕ) {P δ : ℝ} (_hP : 0 ≤ P) (_hδ : 0 < δ) (_hδP : δ⁻¹ ≤ Real.exp P)
    (_hX : (Fintype.card X : ℝ) ≤ P) (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (root : LayerSamplerVariables G I n B → ℤ) (_hroot : ∀ k, |(root k : ℝ)| ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S ρ : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (_hρ : 0 < ρ) (_hρP : 1/ρ ≤ Real.exp P)
    (H : X → ℝ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ H k)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) H Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (W : Option (LayerSamplerVariables G I n B) × X → ℝ) (hW : ∀ z, 0 < W z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ W z)
    (φ : (X → ℝ) → ℂ) (_hφ : ∀ v, ‖φ v‖ ≤ 1),
    let D := VectorPolynomial.selectedCoefficientDensity (G := G) B U b hb o R σ hR hσ L₀
    let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      affineSampleCoefficientTorus U p hm (fun k j => (z (k,j) : ℝ))
    let fiber := fun z => coefficientFiberAverage U μ root D (coefficientEvaluationTorus U root (sample z))
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
      ‖(∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
          (φ (physicalAffineSite root z) * (D (sample z) : ℂ))) -
        (∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
          (φ (physicalAffineSite root z) * (fiber z : ℂ)))‖ ≤ 3*δ := by
  obtain ⟨A, hA, hcomparison⟩ := exists_polynomial_oneSite_comparison m (selectedFourierExponent m)
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U b hb o _ _ μ _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP root hroot p hp hm stride hs Rrank S ρ
    hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth φ hφ
  obtain ⟨F, inst, frequency, c, _, hfreq, hcoeff, happrox⟩ :=
    exists_selected_coefficient_uniform_fourier (G := G) B U b hb o C V hC hV R σ hR hσ hσ1
      Cinv hCinv hchart hsmall L₀ hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP hδ hδP
  let _ := inst
  have hfiber := selectedCoefficientDensity_fiber_integrable (G := G) B U b hb o R σ hR hσ L₀
    C V hC hV hσ1 Cinv hCinv hchart hsmall μ root
  obtain ⟨hZ, he⟩ := hcomparison hP hX hK U μ root hroot frequency hfreq c hcoeff p hp hm stride hs
    hS hSP hρ hδ hρP (by simpa only [one_div] using hδP) hstride H hsize hrank hRrank
    T hT W hW hwidth (VectorPolynomial.selectedCoefficientDensity (G := G) B U b hb o R σ hR hσ L₀)
    hfiber hδ.le happrox φ hφ
  exact ⟨hZ, he.trans_eq (by ring)⟩

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)

noncomputable def translatedSelectedPhysicalDensity {X : Type*}
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) : ℝ :=
  selectedCoefficientDensity B U b hb o R σ hR hσ L₀
    (center + affineSampleCoefficientTorus U p hm (fun k j => (z (k,j) : ℝ)))

theorem translatedSelectedPhysicalDensity_nonneg {X : Type*}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    0 ≤ translatedSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ center p hm z :=
  selectedCoefficientDensity_nonneg B U b hb o R σ hR hσ L₀ _

theorem translatedSelectedPhysicalDensity_measurable_center {X : Type*}
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    Measurable (fun center => translatedSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ center p hm z) :=
  (selectedCoefficientDensity_measurable B U b hb o R σ hR hσ L₀).comp
    (measurable_id.add measurable_const)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem selectedCoefficientDensity_translate_fiber_integrable (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ)+1) * R j ≤ 1/4)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U)) [IsFiniteMeasure μ]
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (t : LayerSamplerVariables G I n B → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => selectedCoefficientDensity B U b hb o R σ hR hσ L₀
      (center + coefficientFiberMap U t y x)) μ := by
  obtain ⟨M, hM⟩ := selectedCoefficientDensity_bounded (G := G) B U b hb o R σ hR hσ L₀
    C V hC hV hσ1 Cinv hCinv hchart hsmall
  apply bounded_coefficient_translate_fiber_integrable U μ _
    (selectedCoefficientDensity_measurable B U b hb o R σ hR hσ L₀) (M := M)
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (hM x).1]
  exact (hM x).2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

theorem exists_selected_sampler_oneSite_domination (m : ℕ) :
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
    let D := selectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ p hm
    let Z := selectedResidueDensityMass stride T W D
    let M := ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hDpos : 0 < Z,
      |Z-1| ≤ 3*δ ∧ 1/2 ≤ Z ∧ Z ≤ 3/2 ∧
      (∀ φ : (X → ℝ) → ℝ, (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) →
        (∑' z, (selectedResidueDensityPMF stride T W hW hZ D
          (selectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀ p hm) hDpos z).toReal *
            φ (physicalAffineSite root z)) ≤
          2*M*(∑' z, (selectedResidueSmoothPMF stride T W hW hZ z).toReal *
            φ (physicalAffineSite root z)) + 6*δ) ∧
      ∀ {Y : Type*} [Fintype Y] (F : (X → ℝ) → Y),
        let base := (selectedResidueFiniteLaw stride T W hW hZ).fiberLaw
          (fun z => F (physicalAffineSite root z.val))
        let tilted := (selectedResidueTiltedFiniteLaw stride T W hW hZ D
          (selectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀ p hm) hDpos).fiberLaw
            (fun z => F (physicalAffineSite root z.val))
        base.excessMass tilted (2*M) ≤ 6*δ ∧
          tilted.mass (Finset.univ.filter (fun y => 2*(2*M)*base.weight y < tilted.weight y)) ≤ 12*δ := by
  obtain ⟨A₀, hA₀, hnorm⟩ := exists_selected_sampler_normalization m
  obtain ⟨A₁, _, hcomparison⟩ := exists_selected_sampler_oneSite_comparison m
  let A := max A₀ A₁
  have hA : 2 ≤ A := hA₀.trans (le_max_left _ _)
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP root hroot p hp hm stride hs Rrank S ρ
    hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth
  have hthreshold (a : ℕ) (ha : a ≤ A) : Real.exp ((P+a)^a) ≤ Real.exp ((P+A)^A) := by
    apply Real.exp_le_exp.mpr
    have haa : (a : ℝ) ≤ A := by exact_mod_cast ha
    have hAr : (2 : ℝ) ≤ A := by exact_mod_cast hA
    exact (pow_le_pow_left₀ (by positivity) (by linarith : P+(a:ℝ) ≤ P+A) a).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ P+A) ha)
  have h₀ := hthreshold A₀ (le_max_left _ _)
  have h₁ := hthreshold A₁ (le_max_right _ _)
  obtain ⟨hZ, hDpos, hclose, hlower, hupper, _⟩ :=
    hnorm B U b hb o μ ν R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
      hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP p hp hm stride hs
      hS hSP hstride hρ hρP H (fun k => h₀.trans (hsize k)) hrank (h₀.trans hRrank) T hT W hW hwidth
  let D := selectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ p hm
  let M := ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
  have htest (φ : (X → ℝ) → ℝ) (hφ : ∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) :
      (∑' z, (selectedResidueDensityPMF stride T W hW hZ D
        (selectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀ p hm) hDpos z).toReal *
          φ (physicalAffineSite root z)) ≤
        2*M*(∑' z, (selectedResidueSmoothPMF stride T W hW hZ z).toReal *
          φ (physicalAffineSite root z)) + 6*δ := by
    have hφn (v : X → ℝ) : ‖(φ v : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ v).1]
      exact (hφ v).2
    obtain ⟨_, he⟩ := hcomparison B U b hb o μ R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
      hP hδ hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP root hroot p hp hm stride hs
      hS hSP hstride hρ hρP H (fun k => h₁.trans (hsize k)) hrank (h₁.trans hRrank)
      T hT W hW hwidth (fun v => (φ v : ℂ)) hφn
    have hcap := selectedCoefficientDensity_fiber_cap (G := G) B U b hb o hR hσ
      (fun j => (V j : ℝ)) (fun j => (V j).coe_nonneg) (fun j => (hV j).2)
      μ ν hσ1 Cinv hCinv hchart hsmall L₀ root
    have hdom := selectedResidueDensityPMF_test_le_of_complex (ε := 3*δ) (a := 1/2) stride T W hW hZ
      (selectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ p hm)
      (fun z => coefficientFiberAverage U μ root
        (VectorPolynomial.selectedCoefficientDensity (G := G) B U b hb o R σ hR hσ L₀)
        (coefficientEvaluationTorus U root (affineSampleCoefficientTorus U p hm (fun k j => (z (k,j) : ℝ)))))
      (fun z => φ (physicalAffineSite root z))
      (selectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀ p hm) hDpos
      (by norm_num) hlower (fun z => (hcap _).2.2) (fun z => (hφ _).1) he
    exact hdom.trans_eq (by ring)
  refine ⟨hZ, hDpos, hclose, hlower, hupper, htest, ?_⟩
  intro Y _ F
  have he := selectedResidue_physical_excess_le root stride T W hW hZ D
    (selectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀ p hm) hDpos htest F
  have ht := selectedResidue_physical_tail_le root stride T W hW hZ D
    (selectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀ p hm) hDpos htest F
  exact ⟨he, ht.trans_eq (by ring)⟩

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

theorem eval_translated_centered_physical {K X V : Type*} [Fintype K]
    [AddCommGroup V] [Module ℝ V] (root : K → ℤ) (N : X → ℕ)
    (p : VectorPolynomial X ℝ V) (z : Option K × X → ℤ) :
    eval (physicalAffineSite root z) (translate (fun i => (integerBoxCenter N i : ℝ)) p) =
      eval (fun i => (centeredIntegerPhysicalSite root N z i : ℝ)) p := by
  rw [centeredIntegerPhysicalSite_cast, eval_translate]
  exact congrArg (fun x : X → ℝ => eval x p) (funext (fun i => add_comm _ _))

theorem exists_translated_sampler_box_domination (m : ℕ) :
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
    (_hwidth : ∀ z, ρ * H z.2 ≤ W z)
    (N : X → ℕ) (_hN : ∀ i, 4 ≤ N i)
    (_hfit : ∀ i, 4*physicalSiteWidth root W i ≤ (N i : ℝ))
    {ρbox : ℝ} (_hρbox : 0 < ρbox) (_hbase : ∀ i, ρbox*(N i : ℝ) ≤ W (none,i))
    (_hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride W z),
    let a : X → ℝ := fun i => (integerBoxCenter N i : ℝ)
    let p' := fun j => translate a (p j)
    let hm' := fun j => coefficients_translate_mem (U j) a (p j) (hm j)
    let D := selectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ p' hm'
    let Z := selectedResidueDensityMass stride T W D
    let M := ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hDpos : 0 < Z,
      |Z-1| ≤ 3*δ ∧ 1/2 ≤ Z ∧ Z ≤ 3/2 ∧
      ∀ φ : (X → ℝ) → ℝ, (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) →
        (∑' z, (selectedResidueDensityPMF stride T W hW hZ D
          (selectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀ p' hm') hDpos z).toReal *
            φ (a + physicalAffineSite root z)) ≤
          2*M*(2*S/ρbox)^Fintype.card X * (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))) + 6*δ := by
  obtain ⟨A, hA, hdom⟩ := exists_selected_sampler_oneSite_domination.{_, _, _, _, _, 0} m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP root hroot p hp hm stride hs Rrank S ρ
    hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth N hN hfit ρbox hρbox hbase hscale
  let a : X → ℝ := fun i => (integerBoxCenter N i : ℝ)
  let p' := fun j => translate a (p j)
  let hm' := fun j => coefficients_translate_mem (U j) a (p j) (hm j)
  have hp' (j) : DegreeLE (1 : X → ℕ) (j.val+1) (p' j) :=
    degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) a (p j) (hp j)
  have hrank' (j) : HasLayerSamplingRank (j.val+1) H Rrank (U j) (p' j) :=
    (hasLayerSamplingRank_translate_iff a (j.val+1) H Rrank (U j) (p j) (hp j)).mpr (hrank j)
  obtain ⟨hZ, hDpos, hclose, hlower, hupper, htest, _⟩ :=
    hdom B U b hb o μ ν R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
      hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP root hroot p' hp' hm' stride hs
      hS hSP hstride hρ hρP H hsize hrank' hRrank T hT W hW hwidth
  obtain ⟨_, href⟩ := exists_selected_reference_box_domination root stride hs T hT W hW hscale
    N hN hfit hS hρbox hstride hbase
  have hM : 0 ≤ ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j) :=
    Finset.prod_nonneg (fun j _ => earlyConstantDensityCap_nonneg _ _ (hR j) (V j).coe_nonneg)
  refine ⟨hZ, hDpos, hclose, hlower, hupper, ?_⟩
  intro φ hφ
  have hb := href φ (fun x _ => (hφ _).1)
  have ht := htest (fun v => φ (a + v)) (fun v => hφ _)
  have hc := add_le_add
    (mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)) (le_refl (6*δ))
  exact ht.trans (by simpa only [mul_assoc] using hc)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

theorem exists_explicit_spatial_sampler (m : ℕ) :
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
    (τ : ℝ) (_hτ : 0 < τ) (_hτ1 : τ ≤ 1) (_hτP : τ⁻¹ ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (N : X → ℕ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ (N k : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun i => (N i : ℝ)) Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let W := centeredSpatialWidths (K := LayerSamplerVariables G I n B) (Real.exp (2*P)) τ N
    let a : X → ℝ := fun i => (integerBoxCenter N i : ℝ)
    let p' := fun j => translate a (p j)
    let hm' := fun j => coefficients_translate_mem (U j) a (p j) (hm j)
    let D := selectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ p' hm'
    let Z := selectedResidueDensityMass stride T W D
    let M := ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
    ∃ hW : ∀ z, 0 < W z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hDpos : 0 < Z,
      |Z-1| ≤ 3*δ ∧ 1/2 ≤ Z ∧ Z ≤ 3/2 ∧
      ∀ φ : (X → ℝ) → ℝ, (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) →
        (∑' z, (selectedResidueDensityPMF stride T W hW hZ D
          (selectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀ p' hm') hDpos z).toReal *
            φ (a + physicalAffineSite root z)) ≤
          2*M*(16*S)^Fintype.card X * (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))) + 6*δ := by
  obtain ⟨A₀, _, hdom⟩ := exists_translated_sampler_box_domination m
  let A := 2*A₀+256
  have hA : 256 ≤ A := by dsimp [A]; omega
  refine ⟨A, by omega, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP root hroot τ hτ hτ1 hτP p hp hm
    stride hs Rrank S hS hSP hstride N hsize hrank hRrank T hT
  have hPQ := le_spatialSamplingBudget hP
  have he := Real.exp_le_exp.mpr hPQ
  have hthreshold := spatial_threshold_dominates hP hA (show 2*A₀ ≤ A by dsimp [A]; omega)
  have hN (i) : 4 ≤ N i := four_le_of_spatial_threshold hP hA (N i) (hsize i)
  let W := centeredSpatialWidths (K := LayerSamplerVariables G I n B) (Real.exp (2*P)) τ N
  have hW : ∀ z, 0 < W z := centeredSpatialWidths_pos (Real.exp_pos _).le hτ N
    (fun i => by have := hN i; omega)
  have hrootSum := root_sum_le_spatial_budget hK root hroot
  have hfit := centeredSpatialWidths_fit (Real.exp_pos (2*P)).le hτ.le hτ1 root hrootSum N
  have hscale := centeredSpatialWidths_scale (K := LayerSamplerVariables G I n B)
    (Real.exp_pos (2*P)).le hτ1 stride hs N (fun i =>
      spatial_scale_of_exp_size hP hτ hτP (Nat.cast_nonneg _) ((hstride i).trans hSP) hAP
        ((spatial_threshold_large hP hA).trans (hsize i)))
  obtain ⟨hZ, hDpos, hclose, hlower, hupper, htest⟩ :=
    hdom B U b hb o μ ν R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
      (hP.trans hPQ) hδ hδsmall (hδP.trans he) (hX.trans hPQ) (hK.trans hPQ)
      (fun j => (hI j).trans hPQ) (fun j => (hn j).trans hPQ) (fun j => (hJ j).trans hPQ)
      (hAP.trans he) (hL₀P.trans he) (fun j => (hCP j).trans he) (fun j => (hVP j).trans he)
      (fun j => (hRP j).trans he) (fun j => (hσP j).trans he)
      root (fun k => (hroot k).trans he) p hp hm stride hs hS (hSP.trans he) hstride
      (spatialWidthFraction_pos P hτ) (spatialWidthFraction_inv_le hP hτ hτP)
      (fun i => (N i : ℝ)) (fun i => hthreshold.trans (hsize i)) hrank (hthreshold.trans hRrank)
      T hT W hW (spatialWidthFraction_mul_le_width P hτ1 N)
      N hN hfit (ρbox := 1/8) (by norm_num)
      (fun i => by dsimp only [W, centeredSpatialWidths]; linarith) hscale
  refine ⟨hW, hZ, hDpos, hclose, hlower, hupper, ?_⟩
  intro φ hφ
  simpa only [show 2*S/(1/8 : ℝ) = 16*S by ring] using htest φ hφ

end Erdos3.BooleanCubeKernel

end

end OAI
