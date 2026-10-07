import OAI.Combinatorics.Progressions.Probability.CommonSectionAmbientDensityMultiple

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped Classical NNReal

theorem exists_allocated_fixed_projected_fourier (m q : ℕ) :
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
      ∀ {T : Type*} [Fintype T]
        (frequency : T → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ) {L : ℝ}, 0 ≤ L →
        (∀ a j e, e.degree ≤ j.val + 1 → ∀ t, |(frequency a j e t : ℝ)| ≤ L) →
        ∃ rows : T → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ,
          (∀ a j s t, |(rows a j s t : ℝ)| ≤ Real.exp ((P + A) ^ A) * L) ∧
          ∀ {X : Type*} (coeff : T → ℂ) {η : ℝ},
            (∀ z, ‖coefficientTorusFourierSum U frequency coeff z - (density z : ℂ)‖ ≤ η) →
            ∀ (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
            (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
            ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j)
              (v : Option (LayerSamplerVariables G I n B) → X → ℝ),
              ‖retainedSiteFourierSum U root dirs frequency rows coeff
                  (affineCoveredSiteSample U root dirs d p hm v) -
                (f (F (affineCoefficientCoverSample U p hm d v)) : ℂ)‖ ≤ η := by
  obtain ⟨A₀, _, hcover⟩ := exists_fixed_kernel_euclidean_density_projected_fourier m q
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget ((X + C (q + 2 + A₀)) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro G _ I _ n B _ J _ U b R σ S c x P hP hG hc hL M hperiod
  let Q := P + (q + 2 : ℕ)
  have hPQ : P ≤ Q := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hbound : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    simpa [Q, Polynomial.eval₂_pow, Nat.cast_add, add_assoc] using hbudget P hP
  obtain ⟨a, ha, _, hperiod⟩ := hperiod
  obtain ⟨d, hd, hdb, hcover⟩ := hcover (fun g => c (.inl g) + (x g none : ℤ))
    (fun i g => (x g (some i) : ℤ)) (a : ℤ) (by exact_mod_cast ha.ne') hperiod hQ (hG.trans hPQ)
    (kernelCubeBox_site_le_exp (fun g => c (.inl g)) x hc hL)
  refine ⟨d, hd, hdb.trans (Real.exp_le_exp.mpr hbound), ?_⟩
  intro y _ _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
  have hs := allocatedCoefficientDensity_positive_spec B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall μ ν
  intro density cap root dirs F cover ξ
  obtain ⟨f, hfc, hfb, hfi, hfm, hflaw, hprojection, hf⟩ := hcover (allocatedPhysicalCubeRoot B U b S c x y) (allocatedPhysicalCubeDirections B U b S x y)
    Sum.inl (fun _ => rfl) (fun _ _ => rfl) U μ ν _ hs.1 hs.2.1 hs.2.2.2.1
  refine ⟨f, hfc, hfb, hfi, hfm, hflaw, hprojection, ?_⟩
  intro T _ frequency L hL hfrequency
  obtain ⟨rows, hrows, happ⟩ := hf frequency hL hfrequency
  refine ⟨rows, ?_, happ⟩
  intro a j s t
  exact (hrows a j s t).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbound) hL)

end Erdos3.VectorPolynomial

end

end OAI
