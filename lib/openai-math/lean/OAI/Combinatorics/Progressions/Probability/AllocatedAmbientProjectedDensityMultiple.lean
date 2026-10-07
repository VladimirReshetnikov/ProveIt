import OAI.Combinatorics.Progressions.Estimates.LowJetAmbientReconstruction

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_fixed_kernel_euclidean_ambient_density (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ)
    (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
    (_hdifference : ∀ i k, difference i (e k) = difference₀ i k)
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {L C : ℝ≥0}
    (_hf : LipschitzWith L f) (_hcap : ∀ z, f z ∈ Set.Icc (0 : ℝ) C)
    (_hmass : (∫ x, f (coefficientAmbientTorus U x) ∂μ) = 1),
    let rows := fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))
    ∃ (g : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
      (F : (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J → UnitAddCircle) → ℝ),
      Continuous g ∧ (∀ y, g y ∈ Set.Icc (0 : ℝ) C) ∧
      Integrable g ξ ∧ (∫ y, g y ∂ξ) = 1 ∧
      (realDensityMeasure μ (fun x => f (coefficientAmbientTorus U (cover x)))).map
        (euclideanCoefficientJetMap U root (Matrix.of difference) rows) = realDensityMeasure ξ g ∧
      (∀ z, F z ∈ Set.Icc (0 : ℝ) C) ∧
      LipschitzWith ((L * (Fintype.card (Finset (Fin q)) *
        Real.toNNReal (Real.exp ((P + A) ^ A)))) *
        ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)) F ∧
      (∀ y, g y = F (coveredJetAmbientTorus U 1 y)) ∧
      physicalDensityProjection U root difference d
        (fun x => f (coefficientAmbientTorus U x)) g := by
  obtain ⟨A, hA, hsource⟩ := exists_fixed_kernel_ambient_density m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite
  obtain ⟨d, hd, hdb, hsource⟩ := hsource root₀ difference₀ a ha hperiod hP hK hsite
  refine ⟨d, hd, hdb, ?_⟩
  intro K _ root difference e hroot hdifference J _ U _ _ _ _ _ μ _ _ ν _ _ f L C hf hcap hmass rows cover ξ
  have hfull := hperiod.trans (integerPeriod_range_le_of_columns
    (Matrix.of difference₀) (Matrix.of difference) e hdifference)
  obtain ⟨g, F, hgc, hgb, _, hgm, hglaw, hFb, hFl, heq, hprojection⟩ :=
    hsource root difference e hroot hdifference U μ f hf hcap hmass
  obtain ⟨hfc, hfb, hfi, hfm, hvalue, hflaw⟩ :=
    siteImage_density_euclideanJet U root (Matrix.of difference) a ha hfull μ ν
      (realDensityMeasure μ (fun x => f (coefficientAmbientTorus U (cover x))))
      g hgc hgb hgm hglaw
  refine ⟨_, fun z => F (lowJetAmbientSites z), hfc, hfb, hfi, hfm, hflaw,
    fun z => hFb _, hFl.comp lowJetAmbientSites_lipschitz, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := euclideanCoefficientJetMap_surjective U root (Matrix.of difference) a ha hfull
      rows (fun _ => Subtype.val_injective) (fun _ o => o.property) y
    exact (hvalue (Set.rangeFactorization
      (coefficientSiteTorusMap U (integerAffineCube root (Matrix.of difference))) x)).trans
      ((heq x).trans (congrArg F (lowJetAmbientSites_coefficient U root (Matrix.of difference) x).symm))
  · intro X Index _ frequency coeff η happrox p hp hm z
    have he := hvalue (Set.rangeFactorization
      (coefficientSiteTorusMap U (integerAffineCube root (Matrix.of difference)))
      (affineCoefficientCoverSample U p hm d z))
    exact (congrArg (fun r : ℝ =>
      ‖affineCubeFourierProjection U root difference frequency p coeff z - (r : ℂ)‖) he).trans_le
      (hprojection frequency coeff happrox p hp hm z)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

theorem exists_allocated_ambient_projected_density (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hc : ∀ g, |(c (.inl g) : ℝ)| ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M),
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + (q + 2 : ℕ) + A) ^ A) ∧
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
    let _ := euclideanCoefficientJetMap U root dirs
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))
    let densityLip := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
      allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip := (Fintype.card (Finset (Fin q)) : ℝ≥0) *
      Real.toNNReal (Real.exp ((P + (q + 2 : ℕ) + A) ^ A))
    let reconstructionLip := ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)
    ∃ (g : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
      (F : (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J → UnitAddCircle) → ℝ),
      Continuous g ∧ (∀ z, g z ∈ Set.Icc (0 : ℝ) cap) ∧ Integrable g ξ ∧
      (∫ z, g z ∂ξ) = 1 ∧
      (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U root dirs
          (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))) =
        realDensityMeasure ξ g ∧
      physicalDensityProjection U root dirs d density g ∧
      (∀ z, F z ∈ Set.Icc (0 : ℝ) cap) ∧
      LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
      ∀ z, g z = F (coveredJetAmbientTorus U 1 z) := by
  obtain ⟨A, hA, hcover⟩ := exists_fixed_kernel_euclidean_ambient_density m q
  refine ⟨A, hA, ?_⟩
  intro G _ I _ n B _ J _ U b R σ S c x P hP hG hc hL M hperiod
  let Q := P + (q + 2 : ℕ)
  have hPQ : P ≤ Q := le_add_of_nonneg_right (Nat.cast_nonneg _)
  obtain ⟨a, ha, _, hperiod⟩ := hperiod
  obtain ⟨d, hd, hdb, hcover⟩ := hcover (fun g => c (.inl g) + (x g none : ℤ))
    (fun i g => (x g (some i) : ℤ)) (a : ℤ) (by exact_mod_cast ha.ne') hperiod
    (hP.trans hPQ) (hG.trans hPQ) (kernelCubeBox_site_le_exp (fun g => c (.inl g)) x hc hL)
  refine ⟨d, hd, hdb, ?_⟩
  intro y _ _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    density cap root dirs unusedJetMap cover ξ densityLip sectionLip reconstructionLip
  have hs := allocatedCoefficientDensity_positive_spec B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall μ ν
  have hambient := allocatedCoefficientAmbientDensity_bounds B U b o S C V hC hV hR hσ
  have heq (z) := allocatedCoefficientAmbientDensity_eq B U b hb o S hR hσ hσ1
    Cinv hCinv hchart hsmall z
  have hm : (∫ z, allocatedCoefficientAmbientDensity B U b o S (coefficientAmbientTorus U z) ∂μ) = 1 := by
    simp_rw [heq]
    exact hs.2.2.2.1
  obtain ⟨g, F, hgc, hgb, hgi, hgm, hglaw, hFb, hFl, hvalue, hprojection⟩ :=
    hcover root dirs Sum.inl (fun _ => rfl) (fun _ _ => rfl) U μ ν
      (allocatedCoefficientAmbientDensity B U b o S) hambient.2
      (C := allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m))
      (fun z => by simpa only [Set.mem_Icc, NNReal.coe_pow] using hambient.1 z) hm
  refine ⟨g, F, hgc, hgb, hgi, hgm, ?_, ?_, hFb, hFl, hvalue⟩
  · simp_rw [heq] at hglaw
    convert hglaw using 1
    rfl
  · intro X Index _ frequency coeff η happ p hp hm v
    apply hprojection frequency coeff ?_ p hp hm v
    intro z
    simpa only [heq] using happ z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_fixed_kernel_euclidean_ambient_density_multiple (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ)
    (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
    (_hdifference : ∀ i k, difference i (e k) = difference₀ i k)
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {L C : ℝ≥0}
    (_hf : LipschitzWith L f) (_hcap : ∀ z, f z ∈ Set.Icc (0 : ℝ) C)
    (_hmass : (∫ x, f (coefficientAmbientTorus U x) ∂μ) = 1),
    let rows := fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))
    ∃ (g : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
      (F : (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J → UnitAddCircle) → ℝ),
      Continuous g ∧ (∀ y, g y ∈ Set.Icc (0 : ℝ) C) ∧
      Integrable g ξ ∧ (∫ y, g y ∂ξ) = 1 ∧
      (realDensityMeasure μ (fun x => f (coefficientAmbientTorus U (cover x)))).map
        (euclideanCoefficientJetMap U root (Matrix.of difference) rows) = realDensityMeasure ξ g ∧
      (∀ z, F z ∈ Set.Icc (0 : ℝ) C) ∧
      LipschitzWith ((L * (Fintype.card (Finset (Fin q)) *
        Real.toNNReal (Real.exp ((P + A) ^ A)))) *
        ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)) F ∧
      (∀ y, g y = F (coveredJetAmbientTorus U 1 y)) ∧
      physicalDensityProjection U root difference d
        (fun x => f (coefficientAmbientTorus U x)) g := by
  obtain ⟨A, hA, hsource⟩ := exists_fixed_kernel_ambient_density_multiple m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite period hp hpP
  obtain ⟨d, hdiv, hd, hdb, hsource⟩ := hsource root₀ difference₀ a ha hperiod hP hK hsite period hp hpP
  refine ⟨d, hdiv, hd, hdb, ?_⟩
  intro K _ root difference e hroot hdifference J _ U _ _ _ _ _ μ _ _ ν _ _ f L C hf hcap hmass rows cover ξ
  have hfull := hperiod.trans (integerPeriod_range_le_of_columns
    (Matrix.of difference₀) (Matrix.of difference) e hdifference)
  obtain ⟨g, F, hgc, hgb, _, hgm, hglaw, hFb, hFl, heq, hprojection⟩ :=
    hsource root difference e hroot hdifference U μ f hf hcap hmass
  obtain ⟨hfc, hfb, hfi, hfm, hvalue, hflaw⟩ :=
    siteImage_density_euclideanJet U root (Matrix.of difference) a ha hfull μ ν
      (realDensityMeasure μ (fun x => f (coefficientAmbientTorus U (cover x))))
      g hgc hgb hgm hglaw
  refine ⟨_, fun z => F (lowJetAmbientSites z), hfc, hfb, hfi, hfm, hflaw,
    fun z => hFb _, hFl.comp lowJetAmbientSites_lipschitz, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := euclideanCoefficientJetMap_surjective U root (Matrix.of difference) a ha hfull
      rows (fun _ => Subtype.val_injective) (fun _ o => o.property) y
    exact (hvalue (Set.rangeFactorization
      (coefficientSiteTorusMap U (integerAffineCube root (Matrix.of difference))) x)).trans
      ((heq x).trans (congrArg F (lowJetAmbientSites_coefficient U root (Matrix.of difference) x).symm))
  · intro X Index _ frequency coeff η happrox p hp hm z
    have he := hvalue (Set.rangeFactorization
      (coefficientSiteTorusMap U (integerAffineCube root (Matrix.of difference)))
      (affineCoefficientCoverSample U p hm d z))
    exact (congrArg (fun r : ℝ =>
      ‖affineCubeFourierProjection U root difference frequency p coeff z - (r : ℂ)‖) he).trans_le
      (hprojection frequency coeff happrox p hp hm z)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

theorem exists_allocated_ambient_projected_density_multiple (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hc : ∀ g, |(c (.inl g) : ℝ)| ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + (q + 2 : ℕ) + A) ^ A) ∧
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
    let _ := euclideanCoefficientJetMap U root dirs
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))
    let densityLip := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
      allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip := (Fintype.card (Finset (Fin q)) : ℝ≥0) *
      Real.toNNReal (Real.exp ((P + (q + 2 : ℕ) + A) ^ A))
    let reconstructionLip := ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)
    ∃ (g : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
      (F : (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J → UnitAddCircle) → ℝ),
      Continuous g ∧ (∀ z, g z ∈ Set.Icc (0 : ℝ) cap) ∧ Integrable g ξ ∧
      (∫ z, g z ∂ξ) = 1 ∧
      (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U root dirs
          (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))) =
        realDensityMeasure ξ g ∧
      physicalDensityProjection U root dirs d density g ∧
      (∀ z, F z ∈ Set.Icc (0 : ℝ) cap) ∧
      LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
      ∀ z, g z = F (coveredJetAmbientTorus U 1 z) := by
  obtain ⟨A, hA, hcover⟩ := exists_fixed_kernel_euclidean_ambient_density_multiple m q
  refine ⟨A, hA, ?_⟩
  intro G _ I _ n B _ J _ U b R σ S c x P hP hG hc hL M hperiod period hp hpP
  let Q := P + (q + 2 : ℕ)
  have hPQ : P ≤ Q := le_add_of_nonneg_right (Nat.cast_nonneg _)
  obtain ⟨a, ha, _, hperiod⟩ := hperiod
  obtain ⟨d, hdiv, hd, hdb, hcover⟩ := hcover (fun g => c (.inl g) + (x g none : ℤ))
    (fun i g => (x g (some i) : ℤ)) (a : ℤ) (by exact_mod_cast ha.ne') hperiod
    (hP.trans hPQ) (hG.trans hPQ) (kernelCubeBox_site_le_exp (fun g => c (.inl g)) x hc hL)
    period hp (hpP.trans (Real.exp_le_exp.mpr hPQ))
  refine ⟨d, hdiv, hd, hdb, ?_⟩
  intro y _ _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    density cap root dirs unusedJetMap cover ξ densityLip sectionLip reconstructionLip
  have hs := allocatedCoefficientDensity_positive_spec B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall μ ν
  have hambient := allocatedCoefficientAmbientDensity_bounds B U b o S C V hC hV hR hσ
  have heq (z) := allocatedCoefficientAmbientDensity_eq B U b hb o S hR hσ hσ1
    Cinv hCinv hchart hsmall z
  have hm : (∫ z, allocatedCoefficientAmbientDensity B U b o S (coefficientAmbientTorus U z) ∂μ) = 1 := by
    simp_rw [heq]
    exact hs.2.2.2.1
  obtain ⟨g, F, hgc, hgb, hgi, hgm, hglaw, hFb, hFl, hvalue, hprojection⟩ :=
    hcover root dirs Sum.inl (fun _ => rfl) (fun _ _ => rfl) U μ ν
      (allocatedCoefficientAmbientDensity B U b o S) hambient.2
      (C := allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m))
      (fun z => by simpa only [Set.mem_Icc, NNReal.coe_pow] using hambient.1 z) hm
  refine ⟨g, F, hgc, hgb, hgi, hgm, ?_, ?_, hFb, hFl, hvalue⟩
  · simp_rw [heq] at hglaw
    convert hglaw using 1
    rfl
  · intro X Index _ frequency coeff η happ p hp hm v
    apply hprojection frequency coeff ?_ p hp hm v
    intro z
    simpa only [heq] using happ z

end Erdos3.VectorPolynomial

end

end OAI
