import OAI.Combinatorics.Progressions.Estimates.CoefficientPairCover
import OAI.Combinatorics.Progressions.Linear.AllocatedOriginalSourceProjection

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [MeasurableSpace (CoefficientTorus (K := K) U)]
variable [BorelSpace (CoefficientTorus (K := K) U)]
variable (R : CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U)
variable (hR : ∀ x ∈ coefficientIntegerLattice U, R x ∈ coefficientIntegerLattice U)
variable (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ]

noncomputable def coefficientResidualAmbientDensity
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ)
    (z : CoefficientAmbientIndex K J → UnitAddCircle) : ℝ :=
  ∫ y, f (z + coefficientAmbientTorus U
    (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) ∂μ

omit [Fintype K] [∀ j, Fintype (J j)] [BorelSpace (CoefficientTorus (K := K) U)]
  [IsProbabilityMeasure μ] in
theorem coefficientResidualAmbientDensity_eq
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ)
    (x : CoefficientTorus (K := K) U) :
    coefficientResidualAmbientDensity U R hR μ f (coefficientAmbientTorus U x) =
      linearQuotientAverage (coefficientIntegerLattice U) R hR μ
        (fun z => f (coefficientAmbientTorus U z)) x := by
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  funext t
  simp only [coefficientAmbientTorus, map_add, Pi.add_apply]

omit [Fintype K] [∀ j, Fintype (J j)] [BorelSpace (CoefficientTorus (K := K) U)] in
theorem coefficientResidualAmbientDensity_bounds
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {C : ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) C) (z) :
    coefficientResidualAmbientDensity U R hR μ f z ∈ Set.Icc (0 : ℝ) C := by
  have h0 : 0 ≤ coefficientResidualAmbientDensity U R hR μ f z :=
    integral_nonneg (fun y => (hf _).1)
  refine ⟨h0, ?_⟩
  have hn := norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall (fun y =>
      show ‖f (z + coefficientAmbientTorus U
        (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y))‖ ≤ C from
      by rw [Real.norm_of_nonneg (hf _).1]; exact (hf _).2))
  change ‖coefficientResidualAmbientDensity U R hR μ f z‖ ≤ C * μ.real Set.univ at hn
  simpa only [probReal_univ, mul_one, Real.norm_of_nonneg h0] using hn

theorem coefficientResidualAmbientDensity_lipschitz
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {L : ℝ≥0}
    (hf : LipschitzWith L f) {C : ℝ} (hfb : ∀ z, ‖f z‖ ≤ C) :
    LipschitzWith L (coefficientResidualAmbientDensity U R hR μ f) := by
  have hRc := linearQuotientEndomorphism_continuous (coefficientIntegerLattice U) R hR
    R.continuous_of_finiteDimensional
  have hi (z : CoefficientAmbientIndex K J → UnitAddCircle) :
      Integrable (fun y => f (z + coefficientAmbientTorus U
        (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y))) μ := by
    apply Integrable.of_bound (C := C)
    · exact (hf.continuous.comp (continuous_const.add
        ((coefficientAmbientTorus_continuous U).comp hRc))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun _ => hfb _)
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Real.dist_eq, ← Real.norm_eq_abs]
  change ‖(∫ y, f (z + coefficientAmbientTorus U
      (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) ∂μ) -
    ∫ y, f (w + coefficientAmbientTorus U
      (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) ∂μ‖ ≤ _
  rw [← integral_sub (hi z) (hi w)]
  calc
    _ ≤ ((L : ℝ) * dist z w) * μ.real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [] with y
      have h := hf.dist_le_mul (z + coefficientAmbientTorus U
        (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y))
        (w + coefficientAmbientTorus U
        (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y))
      rw [dist_add_right] at h
      exact h
    _ = _ := by rw [probReal_univ, mul_one]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

theorem exists_fixed_kernel_density_projected_fourier (m q : ℕ) :
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
        (∀ {I F : Type*} [Fintype F]
          (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ) {η : ℝ},
          (∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η) →
          ∀ (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : Option K → I → ℝ),
            ‖affineCubeFourierProjection U root difference frequency p c z -
              (g (π (affineCoefficientCoverSample U p hm d z)) : ℂ)‖ ≤ η) ∧
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
  refine ⟨g, hgc, hgb, hgi, hgmass, hlaw, ?_, ?_⟩
  · intro I F _ frequency c η happrox p hp hm b
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

theorem exists_fixed_kernel_euclidean_density_projected_fourier (m q : ℕ) :
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
        physicalDensityProjection U root difference d D f ∧
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
  obtain ⟨A, hA, hcover⟩ := exists_fixed_kernel_density_projected_fourier m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite
  obtain ⟨d, hd, hdb, hcover⟩ := hcover root₀ difference₀ a ha hperiod hP hK hsite
  refine ⟨d, hd, hdb, ?_⟩
  intro K _ root difference e hroot hdifference J _ U _ _ _ _ _ μ _ _ ν _ _ D hD B hcap hmass F C ξ
  have hfull := hperiod.trans (integerPeriod_range_le_of_columns
    (Matrix.of difference₀) (Matrix.of difference) e hdifference)
  obtain ⟨g, hgc, hgb, _, hgmass, hglaw, hgprojection, hgapprox⟩ :=
    hcover root difference e hroot hdifference U μ D hD hcap hmass
  obtain ⟨hfc, hfb, hfi, hfmass, hvalue, hflaw⟩ := siteImage_density_euclideanJet U root
    (Matrix.of difference) a ha hfull μ ν (realDensityMeasure μ (fun x => D (C x)))
    g hgc hgb hgmass hglaw
  refine ⟨_, hfc, hfb, hfi, hfmass, hflaw, ?_, ?_⟩
  · intro X G _ frequency coeff η hDapprox p hp hm b
    have he := hvalue (Set.rangeFactorization
      (coefficientSiteTorusMap U (integerAffineCube root (Matrix.of difference)))
      (affineCoefficientCoverSample U p hm d b))
    change (g ((euclideanSiteImageHomeomorph U root (Matrix.of difference) a ha hfull).symm
      (F (affineCoefficientCoverSample U p hm d b)))) = _ at he
    change ‖affineCubeFourierProjection U root difference frequency p coeff b -
      (g ((euclideanSiteImageHomeomorph U root (Matrix.of difference) a ha hfull).symm
        (F (affineCoefficientCoverSample U p hm d b))) : ℂ)‖ ≤ η
    rw [he]
    exact hgprojection frequency coeff hDapprox p hp hm b
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

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

private theorem unitAddCircle_coe_sum {A : Type*} [Fintype A] (a : A → ℝ) :
    ((∑ t, a t : ℝ) : UnitAddCircle) = ∑ t, (a t : UnitAddCircle) :=
  map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) a Finset.univ

variable {K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def coefficientAmbientSiteSection
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)
    (z : JetAmbientIndex (fun _ : Fin m => S) J → UnitAddCircle) :
    CoefficientAmbientIndex K J → UnitAddCircle :=
  fun t => ∑ s, T t.1.1 t.1.2 s • z ⟨t.1.1, s, t.2⟩

noncomputable def coefficientAmbientSiteEvaluation (site : S → K → ℤ)
    (z : CoefficientAmbientIndex K J → UnitAddCircle) :
    JetAmbientIndex (fun _ : Fin m => S) J → UnitAddCircle :=
  fun t => ∑ e, boundedSiteMatrix (t.1.val + 1) site t.2.1 e • z ⟨⟨t.1, e⟩, t.2.2⟩

theorem coefficientAmbientSiteSection_lipschitz
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)
    {L : ℝ≥0} (hT : ∀ j e, ∑ s, ‖T j e s‖ ≤ L) :
    LipschitzWith L (coefficientAmbientSiteSection (J := J) T) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨⟨j, e⟩, i⟩
  calc
    _ ≤ ∑ s, dist (T j e s • z ⟨j,s,i⟩) (T j e s • w ⟨j,s,i⟩) := dist_sum_sum_le _ _ _
    _ ≤ ∑ s, ‖T j e s‖ * dist z w := by
      apply Finset.sum_le_sum
      intro s _
      rw [dist_eq_norm, ← smul_sub]
      exact (norm_zsmul_le _ _).trans (mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using dist_le_pi_dist z w ⟨j,s,i⟩) (norm_nonneg _))
    _ = (∑ s, ‖T j e s‖) * dist z w := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hT j e) dist_nonneg

variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ) (q : ℕ)
variable (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)

local notation "R" => coefficientSiteResidual U site (fun _ => q) T
local notation "hR" => coefficientSiteResidual_preserves_lattice U site (fun _ => q) T

omit [∀ j, Fintype (J j)] in
theorem coefficientAmbientSiteSection_residual (x : CoefficientTorus (K := K) U) :
    coefficientAmbientSiteSection T (coefficientAmbientSiteEvaluation site (coefficientAmbientTorus U x)) +
      coefficientAmbientTorus U (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR x) =
    coefficientAmbientTorus U (quotientIntegerCover (coefficientIntegerLattice U) q x) := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [quotientIntegerCover_mk]
  funext t
  rcases t with ⟨⟨j, e⟩, i⟩
  change (∑ s, T j e s • ∑ a, boundedSiteMatrix (j.val + 1) site s a •
    ((v ⟨j,a⟩).val i : UnitAddCircle)) +
      (((q : ℝ) * (v ⟨j,e⟩).val i -
        (matrixModuleAction (fun a s => (T j a s : ℝ))
          (matrixModuleAction (fun s a => (boundedSiteMatrix (j.val + 1) site s a : ℝ))
            (coefficientLayerArray U j v)) e).val i : ℝ) : UnitAddCircle) =
      (((q : ℝ) * (v ⟨j,e⟩).val i : ℝ) : UnitAddCircle)
  have he : ((matrixModuleAction (fun a s => (T j a s : ℝ))
      (matrixModuleAction (fun s a => (boundedSiteMatrix (j.val + 1) site s a : ℝ))
        (coefficientLayerArray U j v)) e).val i : UnitAddCircle) =
      ∑ s, T j e s • ∑ a, boundedSiteMatrix (j.val + 1) site s a •
        ((v ⟨j,a⟩).val i : UnitAddCircle) := by
    change ((((∑ s : S, (T j e s : ℝ) • ∑ a : BoundedCoefficientExponent K (j.val + 1),
      (boundedSiteMatrix (j.val + 1) site s a : ℝ) • (v ⟨j,a⟩ : U j)) : U j).val i : ℝ) : UnitAddCircle) = _
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, ← zsmul_eq_mul, unitAddCircle_coe_sum, AddCircle.coe_zsmul]
  rw [AddCircle.coe_sub, he]
  exact add_sub_cancel _ _

variable [MeasurableSpace (CoefficientTorus (K := K) U)]
variable [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ]

noncomputable def coefficientSectionAmbientDensity
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ)
    (z : JetAmbientIndex (fun _ : Fin m => S) J → UnitAddCircle) : ℝ :=
  coefficientResidualAmbientDensity U R hR μ f (coefficientAmbientSiteSection T z)

theorem coefficientSectionAmbientDensity_lipschitz
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {L A : ℝ≥0}
    (hf : LipschitzWith L f) {C : ℝ} (hfb : ∀ z, ‖f z‖ ≤ C)
    (hT : ∀ j e, ∑ s, ‖T j e s‖ ≤ A) :
    LipschitzWith (L * A) (coefficientSectionAmbientDensity U site q T μ f) :=
  (coefficientResidualAmbientDensity_lipschitz U R hR μ f hf hfb).comp
    (coefficientAmbientSiteSection_lipschitz T hT)

omit [∀ j, Fintype (J j)] [BorelSpace (CoefficientTorus (K := K) U)] in
theorem coefficientSectionAmbientDensity_bounds
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {C : ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) C) (z) :
    coefficientSectionAmbientDensity U site q T μ f z ∈ Set.Icc (0 : ℝ) C :=
  coefficientResidualAmbientDensity_bounds U R hR μ f hf _

omit [∀ j, Fintype (J j)] [IsProbabilityMeasure μ] in
theorem coefficientSectionAmbientDensity_eq [μ.IsAddLeftInvariant]
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ)
    (x : CoefficientTorus (K := K) U) :
    coefficientSectionAmbientDensity U site q T μ f
      (coefficientAmbientSiteEvaluation site (coefficientAmbientTorus U x)) =
    linearQuotientAverage (coefficientIntegerLattice U) R hR μ
      (fun z => f (coefficientAmbientTorus U z))
      (quotientIntegerCover (coefficientIntegerLattice U) q x) := by
  let r := linearQuotientEndomorphism (coefficientIntegerLattice U) R hR
  have hadd (a b : CoefficientTorus (K := K) U) :
      coefficientAmbientTorus U (r (a + b)) =
        coefficientAmbientTorus U (r a) + coefficientAmbientTorus U (r b) := by
    funext t
    simp only [map_add, coefficientAmbientTorus, Pi.add_apply]
  have hinv (z : CoefficientAmbientIndex K J → UnitAddCircle) :
      coefficientResidualAmbientDensity U R hR μ f (z + coefficientAmbientTorus U (r x)) =
        coefficientResidualAmbientDensity U R hR μ f z := by
    have ht := integral_add_left_eq_self (μ := μ)
      (fun y => f (z + coefficientAmbientTorus U (r y))) x
    simpa only [coefficientResidualAmbientDensity, hadd, add_assoc] using ht
  rw [coefficientSectionAmbientDensity, ← hinv,
    coefficientAmbientSiteSection_residual U site q T x]
  exact coefficientResidualAmbientDensity_eq U R hR μ f _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_fixed_kernel_ambient_density (m q : ℕ) :
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
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {L C : ℝ≥0}
    (_hf : LipschitzWith L f) (_hcap : ∀ z, f z ∈ Set.Icc (0 : ℝ) C)
    (_hmass : (∫ x, f (coefficientAmbientTorus U x) ∂μ) = 1),
    let site := fun s k => affineSite root difference s (some k)
    let E := coefficientSiteTorusMap U site
    let π := Set.rangeFactorization E
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    ∃ (g : Set.range E → ℝ)
      (F : (JetAmbientIndex (fun _ : Fin m => Finset (Fin q)) J → UnitAddCircle) → ℝ),
      Continuous g ∧ (∀ y, g y ∈ Set.Icc (0 : ℝ) C) ∧
      Integrable g (μ.map π) ∧ (∫ y, g y ∂μ.map π) = 1 ∧
      (realDensityMeasure μ (fun x => f (coefficientAmbientTorus U (cover x)))).map π =
        realDensityMeasure (μ.map π) g ∧
      (∀ z, F z ∈ Set.Icc (0 : ℝ) C) ∧
      LipschitzWith (L * (Fintype.card (Finset (Fin q)) *
        Real.toNNReal (Real.exp ((P + A) ^ A)))) F ∧
      (∀ x, g (π x) = F (coefficientAmbientSiteEvaluation site (coefficientAmbientTorus U x))) ∧
      ∀ {X Index : Type*} [Fintype Index]
        (frequency : Index → ∀ j, (K →₀ ℕ) → J j → ℤ) (coeff : Index → ℂ) {η : ℝ},
        (∀ x, ‖coefficientTorusFourierSum U frequency coeff x - (f (coefficientAmbientTorus U x) : ℂ)‖ ≤ η) →
        ∀ (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
        (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
        ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : Option K → X → ℝ),
          ‖affineCubeFourierProjection U root difference frequency p coeff z -
            (g (π (affineCoefficientCoverSample U p hm d z)) : ℂ)‖ ≤ η := by
  obtain ⟨A, hA, hsection⟩ := exists_fixed_kernel_bounded_section m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite
  obtain ⟨d, hd, hdb, hsection⟩ := hsection root₀ difference₀ a ha hperiod hP hK hsite
  refine ⟨d, hd, hdb, ?_⟩
  intro K _ root difference e hroot hdifference J _ U _ _ _ _ _ μ _ _ f L C hf hcap hmass site E π cover
  obtain ⟨T, hTb, hT⟩ := hsection root difference e hroot hdifference
  have hb (z) : ‖f z‖ ≤ C := by rw [Real.norm_of_nonneg (hcap z).1]; exact (hcap z).2
  obtain ⟨g, hgc, hgb, hgi, hgm, hg, hglaw⟩ :=
    exists_covered_coefficient_density U site d hd T (fun j x => hT j x) μ
      (fun x => f (coefficientAmbientTorus U x))
      (hf.continuous.comp (coefficientAmbientTorus_continuous U))
      (fun x => hcap _) hmass
  refine ⟨g, coefficientSectionAmbientDensity U site d T μ f,
    hgc, hgb, hgi, hgm, hglaw,
    coefficientSectionAmbientDensity_bounds U site d T μ f hcap, ?_, ?_, ?_⟩
  · apply coefficientSectionAmbientDensity_lipschitz U site d T μ f hf hb
    intro j i
    have hentry (s) : ‖T j i s‖ ≤ Real.exp ((P + A) ^ A) := by
      have h := (Finset.single_le_sum (fun k _ => abs_nonneg (T j k s : ℝ))
        (Finset.mem_univ i)).trans (hTb j s)
      simpa only [← Int.norm_cast_real, Real.norm_eq_abs] using h
    calc
      _ ≤ ∑ _s : Finset (Fin q), Real.exp ((P + A) ^ A) :=
        Finset.sum_le_sum (fun s _ => hentry s)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        NNReal.coe_mul, NNReal.coe_natCast, Real.toNNReal_of_nonneg (Real.exp_pos _).le]
                  rfl
  · intro x
    exact (hg x).trans (coefficientSectionAmbientDensity_eq U site d T μ f x).symm
  · intro X Index _ frequency coeff η happrox p hp hm z
    let R := coefficientSiteResidual U site (fun _ => d) T
    let hR := coefficientSiteResidual_preserves_lattice U site (fun _ => d) T
    have hfactor (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
        (coefficientArrayFunctional U frequency).comp R = 0 ↔
          affineCubeModeFactors U root difference frequency := by
      change (coefficientArrayFunctional U frequency).comp
        (coefficientSiteResidual U site (fun _ => d) T) = 0 ↔ _
      rw [coefficientSiteResidual_zero_iff U site (fun _ => d) T (fun _ => hd) (fun j x => hT j x),
        affineCubeModeFactors_iff_bounded]
    have he := coefficientTorusFourierProjection_approx_residualAverage U R hR root difference hfactor
      frequency coeff μ (fun x => f (coefficientAmbientTorus U x)) happrox
      (affineSampleCoefficientTorus U p hm z)
      (coefficientResidual_section_integrable U R hR μ _
        (hf.continuous.comp (coefficientAmbientTorus_continuous U)) (fun x => hb _) _)
    have hvalue := hg (affineCoefficientCoverSample U p hm d z)
    rw [affineCoefficientCoverSample_projection U p hm d hd z] at hvalue
    rw [hvalue]
    simpa only [coefficientTorusCharacter_sample U _ p hp hm z, affineCubeFourierProjection] using he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_fixed_kernel_ambient_density_multiple (m q : ℕ) :
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
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {L C : ℝ≥0}
    (_hf : LipschitzWith L f) (_hcap : ∀ z, f z ∈ Set.Icc (0 : ℝ) C)
    (_hmass : (∫ x, f (coefficientAmbientTorus U x) ∂μ) = 1),
    let site := fun s k => affineSite root difference s (some k)
    let E := coefficientSiteTorusMap U site
    let π := Set.rangeFactorization E
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    ∃ (g : Set.range E → ℝ)
      (F : (JetAmbientIndex (fun _ : Fin m => Finset (Fin q)) J → UnitAddCircle) → ℝ),
      Continuous g ∧ (∀ y, g y ∈ Set.Icc (0 : ℝ) C) ∧
      Integrable g (μ.map π) ∧ (∫ y, g y ∂μ.map π) = 1 ∧
      (realDensityMeasure μ (fun x => f (coefficientAmbientTorus U (cover x)))).map π =
        realDensityMeasure (μ.map π) g ∧
      (∀ z, F z ∈ Set.Icc (0 : ℝ) C) ∧
      LipschitzWith (L * (Fintype.card (Finset (Fin q)) *
        Real.toNNReal (Real.exp ((P + A) ^ A)))) F ∧
      (∀ x, g (π x) = F (coefficientAmbientSiteEvaluation site (coefficientAmbientTorus U x))) ∧
      ∀ {X Index : Type*} [Fintype Index]
        (frequency : Index → ∀ j, (K →₀ ℕ) → J j → ℤ) (coeff : Index → ℂ) {η : ℝ},
        (∀ x, ‖coefficientTorusFourierSum U frequency coeff x - (f (coefficientAmbientTorus U x) : ℂ)‖ ≤ η) →
        ∀ (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
        (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
        ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : Option K → X → ℝ),
          ‖affineCubeFourierProjection U root difference frequency p coeff z -
            (g (π (affineCoefficientCoverSample U p hm d z)) : ℂ)‖ ≤ η := by
  obtain ⟨A, hA, hsection⟩ := exists_fixed_kernel_bounded_section_multiple m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite period hp hpP
  obtain ⟨d, hdiv, hd, hdb, hsection⟩ := hsection root₀ difference₀ a ha hperiod hP hK hsite period hp hpP
  refine ⟨d, hdiv, hd, hdb, ?_⟩
  intro K _ root difference e hroot hdifference J _ U _ _ _ _ _ μ _ _ f L C hf hcap hmass site E π cover
  obtain ⟨T, hTb, hT⟩ := hsection root difference e hroot hdifference
  have hb (z) : ‖f z‖ ≤ C := by rw [Real.norm_of_nonneg (hcap z).1]; exact (hcap z).2
  obtain ⟨g, hgc, hgb, hgi, hgm, hg, hglaw⟩ :=
    exists_covered_coefficient_density U site d hd T (fun j x => hT j x) μ
      (fun x => f (coefficientAmbientTorus U x))
      (hf.continuous.comp (coefficientAmbientTorus_continuous U))
      (fun x => hcap _) hmass
  refine ⟨g, coefficientSectionAmbientDensity U site d T μ f,
    hgc, hgb, hgi, hgm, hglaw,
    coefficientSectionAmbientDensity_bounds U site d T μ f hcap, ?_, ?_, ?_⟩
  · apply coefficientSectionAmbientDensity_lipschitz U site d T μ f hf hb
    intro j i
    have hentry (s) : ‖T j i s‖ ≤ Real.exp ((P + A) ^ A) := by
      have h := (Finset.single_le_sum (fun k _ => abs_nonneg (T j k s : ℝ))
        (Finset.mem_univ i)).trans (hTb j s)
      simpa only [← Int.norm_cast_real, Real.norm_eq_abs] using h
    calc
      _ ≤ ∑ _s : Finset (Fin q), Real.exp ((P + A) ^ A) :=
        Finset.sum_le_sum (fun s _ => hentry s)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        NNReal.coe_mul, NNReal.coe_natCast, Real.toNNReal_of_nonneg (Real.exp_pos _).le]
                  rfl
  · intro x
    exact (hg x).trans (coefficientSectionAmbientDensity_eq U site d T μ f x).symm
  · intro X Index _ frequency coeff η happrox p hp hm z
    let R := coefficientSiteResidual U site (fun _ => d) T
    let hR := coefficientSiteResidual_preserves_lattice U site (fun _ => d) T
    have hfactor (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
        (coefficientArrayFunctional U frequency).comp R = 0 ↔
          affineCubeModeFactors U root difference frequency := by
      change (coefficientArrayFunctional U frequency).comp
        (coefficientSiteResidual U site (fun _ => d) T) = 0 ↔ _
      rw [coefficientSiteResidual_zero_iff U site (fun _ => d) T (fun _ => hd) (fun j x => hT j x),
        affineCubeModeFactors_iff_bounded]
    have he := coefficientTorusFourierProjection_approx_residualAverage U R hR root difference hfactor
      frequency coeff μ (fun x => f (coefficientAmbientTorus U x)) happrox
      (affineSampleCoefficientTorus U p hm z)
      (coefficientResidual_section_integrable U R hR μ _
        (hf.continuous.comp (coefficientAmbientTorus_continuous U)) (fun x => hb _) _)
    have hvalue := hg (affineCoefficientCoverSample U p hm d z)
    rw [affineCoefficientCoverSample_projection U p hm d hd z] at hvalue
    rw [hvalue]
    simpa only [coefficientTorusCharacter_sample U _ p hp hm z, affineCubeFourierProjection] using he

end Erdos3.BooleanCubeKernel

end

end OAI
