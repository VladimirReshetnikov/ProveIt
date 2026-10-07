import OAI.Combinatorics.Progressions.Fourier.AllocatedFixedProjectedFourier

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

theorem exists_allocated_projected_reference_jet_mass (m q : ℕ) :
    ∃ A T : ℕ, 2 ≤ A ∧ 2 ≤ T ∧ ∀ {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hc : ∀ g, |(c (.inl g) : ℝ)| ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M),
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)],
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let root := allocatedPhysicalCubeRoot B U b S c x y
    let dirs := allocatedPhysicalCubeDirections B U b S x y
    let F := euclideanCoefficientJetMap U root dirs
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))
    ∃ f : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ,
      Continuous f ∧ (∀ z, f z ∈ Set.Icc (0 : ℝ) cap) ∧ Integrable f ξ ∧
      (∫ z, f z ∂ξ) = 1 ∧
      (realDensityMeasure μ (fun z => density (cover z))).map F = realDensityMeasure ξ f ∧
      physicalDensityProjection U root dirs d density f ∧
      ∀ (_hm : (m : ℝ) ≤ P)
        (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
        (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m,
          (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
        (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
        (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
        (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
        (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P),
        (∀ {δ : ℝ} (_hδ : 0 < δ) (_hδP : δ⁻¹ ≤ Real.exp P),
        let Q := allocatedJetFourierBudget m q A P
        ∃ (Index : Type) (inst : Fintype Index), let _ := inst
        ∃ (frequency : Index → ∀ j, (Fin q →₀ ℕ) → J j → ℤ) (coeff : Index → ℂ),
          (∀ a j e, e.degree ≤ j.val + 1 → ∀ t, |(frequency a j e t : ℝ)| ≤ Real.exp Q) ∧
          (∑ a, ‖coeff a‖) ≤ Real.exp Q ∧
          ∀ z : CoefficientTorus (K := Fin q) U,
            ‖(f (standardPhysicalJetMap U z) : ℂ) - coefficientTorusFourierSum U frequency coeff z‖ ≤ δ) ∧
        ∀ {X : Type*} [Fintype X] [DecidableEq X]
          {Pmass : ℝ} (_hQ : allocatedJetFourierBudget m q A P ≤ Pmass)
          (_hX : (Fintype.card X : ℝ) ≤ Pmass)
          (_hdim : (Fintype.card (Option (Fin q) × X) : ℝ) ≤ Pmass)
          (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
          (hm : ∀ j e, coefficients (p j) e ∈ U j)
          (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
          {Rrank W τ ξ₀ ρ : ℝ} (_hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : ξ₀ ≤ 1) (_hρ : 0 < ρ)
          (_hτP : 1 / τ ≤ Real.exp Pmass) (_hstride : ∀ t, (stride t : ℝ) ≤ Real.exp Pmass)
          (_hsize : ∀ t, Real.exp ((Pmass + T) ^ T) ≤ (N t : ℝ))
          (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
          (_hRank : Real.exp ((Pmass + T) ^ T) ≤ Rrank)
          (_hspatial : ∀ t, 8 * (1 + W) * (stride t : ℝ) * ρ ≤ (ξ₀ * τ) * (N t : ℝ))
          (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
          (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
            (2 * allocatedPhysicalEntryBudget B U b S c)) ≤ ρ)
          (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S))
          (base : X → ℤ)
          (residue : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride),
          let H := trimmedSpatialRootScale τ N stride
          (∑ v ∈ spatialWindow H 4, f (physicalCubeEuclideanSample U d p hm
              (physicalResidueReconstruction (allocatedPhysicalCubeRoot B U b S c x y₀)
                (allocatedPhysicalCubeDirections B U b S x y₀) base
                (boundedColumnResidueRepresentative stride residue) stride v))) ≤
            (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) *
              (∏ t, ∏ _i : Unit ⊕ Fin q, H t) := by
  obtain ⟨A, hA, hdata⟩ := exists_allocated_fixed_projected_fourier m q
  obtain ⟨T, hT, hmass⟩ := exists_coarse_reference_jet_mass m q
  refine ⟨A, T, hA, hT, ?_⟩
  intro G _ I _ n B _ J _ U b R σ S c x P hP hG hc hL M hperiod
  obtain ⟨d, hd, hdb, hdata⟩ := hdata B U b S c x hP hG hc hL hperiod
  refine ⟨d, hd, hdb, ?_⟩
  intro y _ _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    density cap root dirs F cover ξ
  obtain ⟨f, hfc, hfb, hfi, hfm, hflaw, hprojection, hrows⟩ :=
    hdata y hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  have hfourier : ∀ (_hm : (m : ℝ) ≤ P)
        (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
        (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m,
          (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
        (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
        (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
        (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
        (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
        {δ : ℝ} (_hδ : 0 < δ) (_hδP : δ⁻¹ ≤ Real.exp P),
        let Q := allocatedJetFourierBudget m q A P
        ∃ (Index : Type) (inst : Fintype Index), let _ := inst
        ∃ (frequency : Index → ∀ j, (Fin q →₀ ℕ) → J j → ℤ) (coeff : Index → ℂ),
          (∀ a j e, e.degree ≤ j.val + 1 → ∀ t, |(frequency a j e t : ℝ)| ≤ Real.exp Q) ∧
          (∑ a, ‖coeff a‖) ≤ Real.exp Q ∧
          ∀ z : CoefficientTorus (K := Fin q) U,
            ‖(f (standardPhysicalJetMap U z) : ℂ) - coefficientTorusFourierSum U frequency coeff z‖ ≤ δ := by
    intro hm₀ hK hRP hσP hcount hI hn hJ hAP hCP hVP δ hδ hδP Q
    obtain ⟨Index, inst, frequency, coeff, _, hfreq, hcoeff, herr⟩ :=
      exists_allocated_coefficient_uniform_fourier B U b hb o S C V hC hV
        hR hσ hσ1 Cinv hCinv hchart hsmall hP hm₀ hK hRP hσP hcount hI hn hJ
        hAP hL hCP hVP hδ hδP
    let _ := inst
    obtain ⟨rows, hrowsbound, happ⟩ := hrows frequency (Real.exp_pos _).le hfreq
    have hbudget := allocatedJetFourierBudget_dominates m q A hP
    refine ⟨Index, inst, (fun a => sitePullbackFrequency standardPhysicalSite (rows a)),
      retainedSiteCoefficient U root dirs frequency coeff, ?_, ?_, ?_⟩
    · intro a j e _ t
      exact (standardSiteFrequency_bound (rows a) (hrowsbound a) j e t).trans hbudget.2.1
    · exact (retainedSiteCoefficient_norm_sum U root dirs frequency coeff).trans
        (hcoeff.trans hbudget.2.2)
    · obtain ⟨a, ha, _, hperiod⟩ := hperiod
      have hdirs : integerScalarLattice (Fin q) (a : ℤ) ≤ dirs.mulVecLin.range :=
        hperiod.trans (integerPeriod_range_le_of_columns (scalarCubeDifferenceMatrix x) dirs Sum.inl
          (fun _ _ => rfl))
      intro z
      exact sampled_density_standard_fourier U root dirs d hd (a : ℤ)
        (by exact_mod_cast ha.ne') hdirs frequency rows coeff f
        (happ coeff (fun z => by rw [norm_sub_rev]; exact herr z)) z
  refine ⟨f, hfc, hfb, hfi, hfm, hflaw, hprojection, ?_⟩
  intro hm₀ hK hRP hσP hcount hI hn hJ hAP hCP hVP
  refine ⟨fun hδ hδP => hfourier hm₀ hK hRP hσP hcount hI hn hJ hAP hCP hVP hδ hδP, ?_⟩
  intro X _ _ Pmass hQ hX hdim p hp hm N stride hs Rrank W τ ξ₀ ρ hW hτ hξ hρ
    hτP hstride hsize hrank hRank hspatial hρ8 hρshift y₀ base residue H
  obtain ⟨Index, inst, frequency, coeff, hfreq, hcoeff, herr⟩ :=
    hfourier hm₀ hK hRP hσP hcount hI hn hJ hAP hCP hVP
      (show (0 : ℝ) < 1 by norm_num) (by simpa using Real.one_le_exp hP)
  let _ := inst
  have hPmass := (allocatedJetFourierBudget_nonneg m q A hP).trans hQ
  have hN (t : X) : 0 < N t := by
    exact_mod_cast (Real.exp_pos _).trans_le (hsize t)
  have hgeometry := allocatedNarrow_reference_jet_geometry B U b S c x y₀ N stride hN hs
    hW hτ hξ hρ hspatial hρ8 hρshift
  have hcoverP : (d : ℝ) ≤ Real.exp Pmass :=
    hdb.trans (Real.exp_le_exp.mpr ((allocatedJetFourierBudget_dominates m q A hP).1.trans hQ))
  exact hmass hPmass hX hdim U ν frequency
    (fun a j e he t => (hfreq a j e he t).trans (Real.exp_le_exp.mpr hQ)) coeff
    (hcoeff.trans (Real.exp_le_exp.mpr hQ)) p hp hm d hd hcoverP stride hs hτ hτP
    hstride (fun t => (N t : ℝ)) hsize hrank hRank
    (allocatedPhysicalCubeRoot B U b S c x y₀) (allocatedPhysicalCubeDirections B U b S x y₀)
    base residue H (fun t => (hgeometry t).1) (fun t => (hgeometry t).2.1)
    (fun t => (hgeometry t).2.2.1) (fun t => (hgeometry t).2.2.2)
    f (fun z => (hfb z).1) hfi hfm herr

end Erdos3.VectorPolynomial

end

end OAI
