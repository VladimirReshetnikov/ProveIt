import OAI.Combinatorics.Progressions.Sampling.ExplicitSpatialSampler

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators NNReal

theorem exists_translated_selected_sampler_normalization (m : ℕ) :
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
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
      ∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
      let D := translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ center p hm
      let Z := selectedResidueDensityMass stride T W D
      0 < Z ∧ |Z-1| ≤ 3*δ ∧ 1/2 ≤ Z ∧ Z ≤ 3/2 ∧
      ∃ q : PMF (Option (LayerSamplerVariables G I n B) × X → ℤ),
        ∀ z, (q z).toReal = (selectedResidueSmoothPMF stride T W hW hZ z).toReal * D z / Z := by
  obtain ⟨A, hA, hmass⟩ := exists_polynomial_coefficient_density_mass m (selectedFourierExponent m)
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP p hp hm stride hs Rrank S ρ
    hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth
  let scale := selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀
  let D₀ := selectedCoefficientDensity (G := G) B U b hb o R σ hR hσ L₀
  have hspec := allocatedCoefficientDensity_spec B U b hb o hR hσ scale
    hσ1 Cinv hCinv hchart hsmall μ ν
  obtain ⟨F, inst, frequency, c, _, hfreq, hcoeff, happrox⟩ :=
    exists_selected_coefficient_uniform_fourier (G := G) B U b hb o C V hC hV R σ hR hσ hσ1
      Cinv hCinv hchart hsmall L₀ hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP hδ hδP
  let _ := inst
  have hcenter (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :=
    hmass hP hX hK U μ frequency hfreq
      (fun a => c a * coefficientTorusCharacter U (frequency a) center)
      (by rw [coefficientFourier_translate_norm]; exact hcoeff)
      p hp hm stride hs hS hSP hρ hδ hρP (by simpa only [one_div] using hδP)
      hstride H hsize hrank hRrank T hT W hW hwidth (fun x => D₀ (center+x))
      (hspec.2.2.1.comp_add_left center)
      ((integral_add_left_eq_self (μ := μ) D₀ center).trans hspec.2.2.2.1)
      hδ.le (coefficientFourier_translate_approx U D₀ frequency c happrox center)
  obtain ⟨hZ, _⟩ := hcenter 0
  refine ⟨hZ, ?_⟩
  intro center
  obtain ⟨_, hclose⟩ := hcenter center
  let D := translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ center p hm
  let Z := selectedResidueDensityMass stride T W D
  change |Z-1| ≤ 2*δ+δ at hclose
  have hclose' : |Z-1| ≤ 3*δ := by linarith
  have hlower : 1/2 ≤ Z := by have h := (abs_le.mp hclose').1; linarith
  have hupper : Z ≤ 3/2 := by have h := (abs_le.mp hclose').2; linarith
  have hpos : 0 < Z := by linarith
  have hD0 := translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀ center p hm
  refine ⟨hpos, hclose', hlower, hupper, selectedResidueDensityPMF stride T W hW hZ D hD0 hpos, ?_⟩
  exact selectedResidueDensityPMF_toReal stride T W hW hZ D hD0 hpos

end Erdos3.VectorPolynomial

end

end OAI
