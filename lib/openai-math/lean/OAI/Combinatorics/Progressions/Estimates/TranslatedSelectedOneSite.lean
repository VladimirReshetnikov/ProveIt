import OAI.Combinatorics.Progressions.Sampling.ExplicitSpatialSampler

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

theorem exists_translated_selected_sampler_oneSite_comparison (m : ℕ) :
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
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (φ : (X → ℝ) → ℂ) (_hφ : ∀ v, ‖φ v‖ ≤ 1),
    let D := fun x => VectorPolynomial.selectedCoefficientDensity (G := G) B U b hb o R σ hR hσ L₀ (center+x)
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
    hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth center φ hφ
  obtain ⟨F, inst, frequency, c, _, hfreq, hcoeff, happrox⟩ :=
    exists_selected_coefficient_uniform_fourier (G := G) B U b hb o C V hC hV R σ hR hσ hσ1
      Cinv hCinv hchart hsmall L₀ hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP hδ hδP
  let _ := inst
  let D₀ := VectorPolynomial.selectedCoefficientDensity (G := G) B U b hb o R σ hR hσ L₀
  have hfiber := selectedCoefficientDensity_translate_fiber_integrable (G := G) B U b hb o R σ hR hσ L₀
    C V hC hV hσ1 Cinv hCinv hchart hsmall μ center root
  obtain ⟨hZ, he⟩ := hcomparison hP hX hK U μ root hroot frequency hfreq
    (fun a => c a * coefficientTorusCharacter U (frequency a) center)
    (by rw [coefficientFourier_translate_norm]; exact hcoeff)
    p hp hm stride hs hS hSP hρ hδ hρP (by simpa only [one_div] using hδP)
    hstride H hsize hrank hRrank T hT W hW hwidth (fun x => D₀ (center+x))
    hfiber hδ.le (coefficientFourier_translate_approx U D₀ frequency c happrox center) φ hφ
  exact ⟨hZ, he.trans_eq (by ring)⟩

end Erdos3.BooleanCubeKernel

end

end OAI
