import OAI.Combinatorics.Progressions.Estimates.MixedSelectedOneSite

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

theorem exists_mixed_selected_sampler_uniform_box_law (m : ℕ) :
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
    (N margin : X → ℕ) (_hmargin : ∀ i, 2 * margin i < N i)
    (_hfit : ∀ i, physicalSiteWidth root W i ≤ (margin i : ℝ)),
    let pa := fun (a : X → ℤ) j => translate (fun i => (a i : ℝ)) (p j)
    let hma := fun (a : X → ℤ) j => coefficients_translate_mem (U j) (fun i => (a i : ℝ)) (p j) (hm j)
    let D := fun a center => translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀
      (coefficientConstantCenter U center) (pa a) (hma a)
    let Z := fun a center => selectedResidueDensityMass stride T W (D a center)
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : ∀ a center, 0 < Z a center,
      (∀ a center, |Z a center-1| ≤ 3*δ ∧ 1/2 ≤ Z a center ∧ Z a center ≤ 3/2) ∧
      ∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
        ‖(𝔼 a ∈ trimmedIntegerBox N margin,
          ∫ center, ∑' z, ((selectedResidueDensityPMF stride T W hW hZ (D a center)
            (translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
              (coefficientConstantCenter U center) (pa a) (hma a)) (hD a center) z).toReal : ℂ) *
              φ ((fun i => (a i : ℝ)) + physicalAffineSite root z) ∂μ) -
            (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
          6*δ + 2 * ∑ i, 2 * (margin i : ℝ) / N i := by
  obtain ⟨A, hA, hlaw⟩ := exists_mixed_center_selected_sampler_oneSite_law m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP root hroot p hp hm stride hs Rrank S ρ
    hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth N margin hmargin hfit
  let pa := fun (a : X → ℤ) j => translate (fun i => (a i : ℝ)) (p j)
  let hma := fun (a : X → ℤ) j => coefficients_translate_mem (U j) (fun i => (a i : ℝ)) (p j) (hm j)
  have hlocal (a : X → ℤ) := hlaw B U b hb o μ ν R σ hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall L₀ hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP
    root hroot (pa a)
    (fun j => degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j))
    (hma a) stride hs hS hSP hstride hρ hρP H hsize
    (fun j => (hasLayerSamplingRank_translate_iff _ _ H Rrank (U j) (p j) (hp j)).mpr (hrank j))
    hRrank T hT W hW hwidth
  choose hZ hD hrest using hlocal
  refine ⟨hZ 0, hD, fun a => (hrest a).1, ?_⟩
  intro φ hφ
  refine selectedResidue_trimmed_comparison_transfer root N margin hmargin stride T W hW (hZ 0)
    hfit (fun x => φ (fun i => (x i : ℝ))) (fun x _ => hφ _) _ ?_
  intro a _
  have h := (hrest a).2 (fun v => φ ((fun i => (a i : ℝ)) + v)) (fun v => hφ _)
  have hcast (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
      (fun i => ((a + integerPhysicalSite root z) i : ℝ)) =
        (fun i => (a i : ℝ)) + physicalAffineSite root z := by
    funext i
    simp only [Pi.add_apply, Int.cast_add, integerPhysicalSite_cast_apply]
  simpa only [hcast] using h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

theorem exists_explicit_mixed_uniform_box_sampler (m : ℕ) :
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
    (τ : ℝ) (_hτ : 0 < τ) (_hτhalf : τ ≤ 1/2) (_hτP : τ⁻¹ ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (N : X → ℕ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ (N k : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun i => (N i : ℝ)) Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let W := trimmedSpatialWidths (K := LayerSamplerVariables G I n B) (Real.exp (2*P)) τ N
    let margin := spatialTrimMargin τ N
    let pa := fun (a : X → ℤ) j => translate (fun i => (a i : ℝ)) (p j)
    let hma := fun (a : X → ℤ) j => coefficients_translate_mem (U j) (fun i => (a i : ℝ)) (p j) (hm j)
    let D := fun a center => translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀
      (coefficientConstantCenter U center) (pa a) (hma a)
    let Z := fun a center => selectedResidueDensityMass stride T W (D a center)
    ∃ hW : ∀ z, 0 < W z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : ∀ a center, 0 < Z a center,
      (∀ a center, |Z a center-1| ≤ 3*δ ∧ 1/2 ≤ Z a center ∧ Z a center ≤ 3/2) ∧
      ∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
        ‖(𝔼 a ∈ trimmedIntegerBox N margin,
          ∫ center, ∑' z, ((selectedResidueDensityPMF stride T W hW hZ (D a center)
            (translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
              (coefficientConstantCenter U center) (pa a) (hma a)) (hD a center) z).toReal : ℂ) *
              φ ((fun i => (a i : ℝ)) + physicalAffineSite root z) ∂μ) -
            (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
          6*δ + 2 * (Fintype.card X : ℝ) * τ := by
  obtain ⟨A₀, _, hlaw⟩ := exists_mixed_selected_sampler_uniform_box_law m
  let A := 2*A₀+256
  have hA : 256 ≤ A := by dsimp [A]; omega
  refine ⟨A, by omega, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP root hroot τ hτ hτhalf hτP p hp hm
    stride hs Rrank S hS hSP hstride N hsize hrank hRrank T hT
  have hPQ := le_spatialSamplingBudget hP
  have he := Real.exp_le_exp.mpr hPQ
  have hthreshold := spatial_threshold_dominates hP hA (show 2*A₀ ≤ A by dsimp [A]; omega)
  have hN (i) : 0 < N i := by
    have := four_le_of_spatial_threshold hP hA (N i) (hsize i)
    omega
  have hmarginSize (i) : 4 ≤ τ * (N i : ℝ) :=
    spatialTrimMargin_size_of_exp_size hP hτ hτP
      ((spatial_threshold_large hP hA).trans (hsize i))
  let W := trimmedSpatialWidths (K := LayerSamplerVariables G I n B) (Real.exp (2*P)) τ N
  have hW : ∀ z, 0 < W z := trimmedSpatialWidths_pos (Real.exp_pos _).le hτ N hN
  have hrootSum := root_sum_le_spatial_budget hK root hroot
  obtain ⟨hZ, hD, hclose, htest⟩ :=
    hlaw B U b hb o μ ν R σ hR hσ hσ1 C V hC hV
      Cinv hCinv hchart hsmall L₀ (hP.trans hPQ) hδ hδsmall (hδP.trans he)
      (hX.trans hPQ) (hK.trans hPQ)
      (fun j => (hI j).trans hPQ) (fun j => (hn j).trans hPQ) (fun j => (hJ j).trans hPQ)
      (hAP.trans he) (hL₀P.trans he) (fun j => (hCP j).trans he) (fun j => (hVP j).trans he)
      (fun j => (hRP j).trans he) (fun j => (hσP j).trans he)
      root (fun k => (hroot k).trans he) p hp hm stride hs hS (hSP.trans he) hstride
      (spatialWidthFraction_pos P hτ) (spatialWidthFraction_inv_le hP hτ hτP)
      (fun i => (N i : ℝ)) (fun i => hthreshold.trans (hsize i)) hrank (hthreshold.trans hRrank)
      T hT W hW (spatialWidthFraction_le_trimmed_width P hτ.le N)
      N (spatialTrimMargin τ N) (spatialTrimMargin_proper hτhalf N hN hmarginSize)
      (spatialTrimMargin_fits (Real.exp_pos _).le hτ.le root hrootSum N)
  refine ⟨hW, hZ, hD, hclose, ?_⟩
  intro φ hφ
  exact (htest φ hφ).trans (add_le_add (le_refl (6*δ))
    (spatialTrimMargin_error_bound N hN hmarginSize))

end Erdos3.BooleanCubeKernel

end

end OAI
