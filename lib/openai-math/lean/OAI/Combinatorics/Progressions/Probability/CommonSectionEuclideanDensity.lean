import OAI.Combinatorics.Progressions.Linear.FixedKernelEuclideanDensity

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

theorem exists_fixed_kernel_density_site_fourier (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
      ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ)
      (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
      (_hdifference : ∀ i k, difference i (e k) = difference₀ i k)
      {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
      [CompactSpace (CoefficientTorus (K := K) U)]
      [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
      [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
      (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
      (D : CoefficientTorus (K := K) U → ℝ), Continuous D →
      ∀ {B : ℝ}, (∀ x, D x ∈ Set.Icc (0 : ℝ) B) → (∫ x, D x ∂μ) = 1 →
      let E := coefficientSiteTorusMap U (fun s k => affineSite root difference s (some k))
      let π := Set.rangeFactorization E
      let C := quotientIntegerCover (coefficientIntegerLattice U) d
      ∃ g : Set.range E → ℝ, Continuous g ∧ (∀ y, g y ∈ Set.Icc (0 : ℝ) B) ∧
        Integrable g (μ.map π) ∧ (∫ y, g y ∂μ.map π) = 1 ∧
        (realDensityMeasure μ (fun x => D (C x))).map π = realDensityMeasure (μ.map π) g ∧
        ∀ {F : Type*} [Fintype F]
          (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) {L : ℝ}, 0 ≤ L →
          (∀ a j e, e.degree ≤ j.val + 1 → ∀ t, |(frequency a j e t : ℝ)| ≤ L) →
          ∃ b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ,
            (∀ a j s t, |(b a j s t : ℝ)| ≤ Real.exp ((P + A) ^ A) * L) ∧
            ∀ {I : Type*} (c : F → ℂ) {η : ℝ},
              (∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η) →
              ∀ (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)),
              (∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j)) →
              ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : Option K → I → ℝ),
                ‖retainedSiteFourierSum U root difference frequency b c
                    (affineCoveredSiteSample U root difference d p hm z) -
                  (g (π (affineCoefficientCoverSample U p hm d z)) : ℂ)‖ ≤ η := by
  obtain ⟨A, hA, hresidual⟩ := exists_fixed_kernel_bounded_section m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite
  obtain ⟨d, hd, hdb, hextend⟩ := hresidual root₀ difference₀ a ha hperiod hP hK hsite
  refine ⟨d, hd, hdb, ?_⟩
  intro K _ root difference e hroot hdifference
  obtain ⟨T, hTb, hT⟩ := hextend root difference e hroot hdifference
  let site := fun s k => affineSite root difference s (some k)
  intro J _ U _ _ _ _ _ μ _ _ D hD B hcap hmass E π C
  let R := coefficientSiteResidual U site (fun _ => d) T
  let hR := coefficientSiteResidual_preserves_lattice U site (fun _ => d) T
  obtain ⟨g, hgc, hgb, hgi, hgmass, hg, hlaw⟩ :=
    exists_covered_coefficient_density U site d hd T (fun j x => hT j x) μ D hD hcap hmass
  refine ⟨g, hgc, hgb, hgi, hgmass, hlaw, ?_⟩
  intro F _ frequency L hL hfrequency
  refine ⟨fun a => sectionSiteFrequency T (frequency a), ?_, ?_⟩
  · intro a j s t
    exact sectionSiteFrequency_bound T (frequency a) hL hTb (hfrequency a) j s t
  intro I c η happrox p hp hm b
  rw [← section_retained_fourier_sum U root difference d hd T (fun j x => hT j x)
    frequency c p hp hm b]
  have hfactor (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
      (coefficientArrayFunctional U frequency).comp R = 0 ↔
        affineCubeModeFactors U root difference frequency := by
    change (coefficientArrayFunctional U frequency).comp
      (coefficientSiteResidual U site (fun _ => d) T) = 0 ↔ _
    rw [coefficientSiteResidual_zero_iff U site (fun _ => d) T (fun _ => hd) (fun j x => hT j x),
      affineCubeModeFactors_iff_bounded]
  have hb (x) : ‖D x‖ ≤ B := by rw [Real.norm_of_nonneg (hcap x).1]; exact (hcap x).2
  have he := coefficientTorusFourierProjection_approx_residualAverage U R hR root difference hfactor
    frequency c μ D happrox (affineSampleCoefficientTorus U p hm b)
    (coefficientResidual_section_integrable U R hR μ D hD hb _)
  have hvalue := hg (affineCoefficientCoverSample U p hm d b)
  rw [affineCoefficientCoverSample_projection U p hm d hd b] at hvalue
  rw [hvalue]
  simpa only [coefficientTorusCharacter_sample U _ p hp hm b, affineCubeFourierProjection] using he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped Classical

theorem exists_fixed_kernel_euclidean_density_fourier (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
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
      (D : CoefficientTorus (K := K) U → ℝ), Continuous D →
      ∀ {B : ℝ}, (∀ x, D x ∈ Set.Icc (0 : ℝ) B) → (∫ x, D x ∂μ) = 1 →
      let F := euclideanCoefficientJetMap U root (Matrix.of difference)
        (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
      let C := quotientIntegerCover (coefficientIntegerLattice U) d
      let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))
      ∃ f : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ,
        Continuous f ∧ (∀ z, f z ∈ Set.Icc (0 : ℝ) B) ∧ Integrable f ξ ∧
        (∫ z, f z ∂ξ) = 1 ∧
        (realDensityMeasure μ (fun x => D (C x))).map F = realDensityMeasure ξ f ∧
        ∀ {G : Type*} [Fintype G]
          (frequency : G → ∀ j, (K →₀ ℕ) → J j → ℤ) {L : ℝ}, 0 ≤ L →
          (∀ a j e, e.degree ≤ j.val + 1 → ∀ t, |(frequency a j e t : ℝ)| ≤ L) →
          ∃ b : G → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ,
            (∀ a j s t, |(b a j s t : ℝ)| ≤ Real.exp ((P + A) ^ A) * L) ∧
            ∀ {I : Type*} (c : G → ℂ) {η : ℝ},
              (∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η) →
              ∀ (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)),
              (∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j)) →
              ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : Option K → I → ℝ),
                ‖retainedSiteFourierSum U root difference frequency b c
                    (affineCoveredSiteSample U root difference d p hm z) -
                  (f (F (affineCoefficientCoverSample U p hm d z)) : ℂ)‖ ≤ η := by
  obtain ⟨A, hA, hcover⟩ := exists_fixed_kernel_density_site_fourier m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite
  obtain ⟨d, hd, hdb, hcover⟩ := hcover root₀ difference₀ a ha hperiod hP hK hsite
  refine ⟨d, hd, hdb, ?_⟩
  intro K _ root difference e hroot hdifference J _ U _ _ _ _ _ μ _ _ ν _ _ D hD B hcap hmass F C ξ
  have hfull := hperiod.trans (integerPeriod_range_le_of_columns
    (Matrix.of difference₀) (Matrix.of difference) e hdifference)
  obtain ⟨g, hgc, hgb, _, hgmass, hglaw, hgapprox⟩ :=
    hcover root difference e hroot hdifference U μ D hD hcap hmass
  obtain ⟨hfc, hfb, hfi, hfmass, hvalue, hflaw⟩ := siteImage_density_euclideanJet U root
    (Matrix.of difference) a ha hfull μ ν (realDensityMeasure μ (fun x => D (C x)))
    g hgc hgb hgmass hglaw
  refine ⟨_, hfc, hfb, hfi, hfmass, hflaw, ?_⟩
  intro G _ frequency L hL hfrequency
  obtain ⟨rows, hrows, happrox⟩ := hgapprox frequency hL hfrequency
  refine ⟨rows, hrows, ?_⟩
  intro I c η hDapprox p hp hm b
  have he := hvalue (Set.rangeFactorization
    (coefficientSiteTorusMap U (integerAffineCube root (Matrix.of difference)))
    (affineCoefficientCoverSample U p hm d b))
  change (g ((euclideanSiteImageHomeomorph U root (Matrix.of difference) a ha hfull).symm
    (F (affineCoefficientCoverSample U p hm d b)))) = _ at he
  rw [he]
  exact happrox c hDapprox p hp hm b

end Erdos3.BooleanCubeKernel

end

end OAI
