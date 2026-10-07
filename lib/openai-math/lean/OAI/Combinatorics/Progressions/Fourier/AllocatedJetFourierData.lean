/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Probability.AllocatedFixedPositiveDensity
import OAI.Combinatorics.Progressions.Probability.CommonSectionEuclideanDensity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem sitePullbackFrequency_unit_bound {K S : Type*} [Fintype S] {m : ℕ}
    {J : Fin m → Type*} (site : S → K → ℤ) (b : ∀ j, Matrix S (J j) ℤ)
    (hsite : ∀ s k, |(site s k : ℝ)| ≤ 1) {B : ℝ}
    (hb : ∀ j s a, |(b j s a : ℝ)| ≤ B)
    (j : Fin m) (e : K →₀ ℕ) (a : J j) :
    |(sitePullbackFrequency site b j e a : ℝ)| ≤ Fintype.card S * B := by
  have hmon (s : S) : |((e.prod (fun k n => site s k ^ n) : ℤ) : ℝ)| ≤ 1 := by
    simp only [Finsupp.prod, Int.cast_prod, Int.cast_pow, Finset.abs_prod, abs_pow]
    exact Finset.prod_le_one₀ (fun k _ => pow_nonneg (abs_nonneg _) _)
      (fun k _ => pow_le_one₀ (abs_nonneg _) (hsite s k))
  simp only [sitePullbackFrequency, Int.cast_sum, Int.cast_mul]
  calc
    _ ≤ ∑ s, |((e.prod (fun k n => site s k ^ n) : ℤ) : ℝ) * (b j s a : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s : S, B := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul]
      exact (mul_le_mul (hmon s) (hb j s a) (abs_nonneg _) (by norm_num)).trans_eq (one_mul B)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Erdos3.VectorPolynomial

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

theorem standardPhysicalSite_bound {q : ℕ} (s : Finset (Fin q)) (i : Fin q) :
    |(standardPhysicalSite s i : ℝ)| ≤ 1 := by
  by_cases hi : i ∈ s <;> simp [standardPhysicalSite, integerAffineCube, Matrix.one_apply, hi]

theorem standardSiteFrequency_bound {m q : ℕ} {J : Fin m → Type*}
    (b : ∀ j, Matrix (Finset (Fin q)) (J j) ℤ) {B : ℝ}
    (hb : ∀ j s a, |(b j s a : ℝ)| ≤ B) (j : Fin m) (e : Fin q →₀ ℕ) (a : J j) :
    |(sitePullbackFrequency standardPhysicalSite b j e a : ℝ)| ≤ (2 : ℝ) ^ q * B := by
  simpa only [Fintype.card_finset, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using
    sitePullbackFrequency_unit_bound standardPhysicalSite b standardPhysicalSite_bound hb j e a

noncomputable def retainedSiteCoefficient {K F : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ) (a : F) : ℂ :=
  if affineCubeModeFactors U root difference (frequency a) then c a else 0

theorem retainedSiteCoefficient_norm_sum {K F : Type*} [Fintype K] [Fintype F] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ) :
    (∑ a, ‖retainedSiteCoefficient U root difference frequency c a‖) ≤ ∑ a, ‖c a‖ := by
  apply Finset.sum_le_sum
  intro a _
  unfold retainedSiteCoefficient
  split_ifs <;> simp

theorem retainedSiteFourierSum_standard {K F : Type*} [Fintype K] [Fintype F] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ) (c : F → ℂ)
    (y : CoefficientTorus (K := Fin q) U) :
    retainedSiteFourierSum U root difference frequency b c
        (coefficientSiteTorusMap U standardPhysicalSite y) =
      coefficientTorusFourierSum U (fun a => sitePullbackFrequency standardPhysicalSite (b a))
        (retainedSiteCoefficient U root difference frequency c) y := by
  rw [← siteTorusFourierSum_pullback]
  unfold retainedSiteFourierSum siteTorusFourierSum retainedSiteCoefficient
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem sampled_density_standard_fourier {K F : Type*} [Fintype K] [Fintype F] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (d : ℕ) (hd : 0 < d)
    (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference).mulVecLin.range)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (rows : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ) (c : F → ℂ)
    (g : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    {η : ℝ}
    (happrox : ∀ (p : ∀ j, VectorPolynomial K ℝ (J j → ℝ)),
      (∀ j, DegreeLE (1 : K → ℕ) (j.val + 1) (p j)) →
      ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : Option K → K → ℝ),
        ‖retainedSiteFourierSum U root difference frequency rows c
            (affineCoveredSiteSample U root difference d p hm z) -
          (g (euclideanCoefficientJetMap U root (Matrix.of difference)
            (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
            (affineCoefficientCoverSample U p hm d z)) : ℂ)‖ ≤ η)
    (y : CoefficientTorus (K := Fin q) U) :
    ‖(g (standardPhysicalJetMap U y) : ℂ) -
      coefficientTorusFourierSum U (fun i => sitePullbackFrequency standardPhysicalSite (rows i))
        (retainedSiteCoefficient U root difference frequency c) y‖ ≤ η := by
  have hglobal := sampled_jet_approximation_global U root difference d hd
    (retainedSiteFourierSum U root difference frequency rows c) g happrox
  have h := standard_jet_site_approximation U root (Matrix.of difference) a ha hperiod
    (retainedSiteFourierSum U root difference frequency rows c) g hglobal y
  rw [retainedSiteFourierSum_standard] at h
  rw [norm_sub_rev]
  exact h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped Classical NNReal

theorem exists_allocated_fixed_positive_fourier (m q : ℕ) :
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
  obtain ⟨A₀, _, hcover⟩ := exists_fixed_kernel_euclidean_density_fourier m q
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
  obtain ⟨f, hfc, hfb, hfi, hfm, hflaw, hf⟩ := hcover (allocatedPhysicalCubeRoot B U b S c x y) (allocatedPhysicalCubeDirections B U b S x y)
    Sum.inl (fun _ => rfl) (fun _ _ => rfl) U μ ν _ hs.1 hs.2.1 hs.2.2.2.1
  refine ⟨f, hfc, hfb, hfi, hfm, hflaw, ?_⟩
  intro T _ frequency L hL hfrequency
  obtain ⟨rows, hrows, happ⟩ := hf frequency hL hfrequency
  refine ⟨rows, ?_, happ⟩
  intro a j s t
  exact (hrows a j s t).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbound) hL)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

theorem exists_allocated_uniform_jet_fourier (m q : ℕ) :
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
      ∀ {T : Type*} [Fintype T]
        (frequency : T → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ) {L : ℝ}, 0 ≤ L →
        (∀ a j e, e.degree ≤ j.val + 1 → ∀ t, |(frequency a j e t : ℝ)| ≤ L) →
        ∃ frequency' : T → ∀ j, (Fin q →₀ ℕ) → J j → ℤ,
          (∀ a j e, e.degree ≤ j.val + 1 → ∀ t,
            |(frequency' a j e t : ℝ)| ≤ (2 : ℝ) ^ q * (Real.exp ((P + A) ^ A) * L)) ∧
          ∀ (coeff : T → ℂ) {η : ℝ},
            (∀ z, ‖coefficientTorusFourierSum U frequency coeff z - (density z : ℂ)‖ ≤ η) →
            ∃ coeff' : T → ℂ, (∑ a, ‖coeff' a‖) ≤ ∑ a, ‖coeff a‖ ∧
              ∀ z : CoefficientTorus (K := Fin q) U,
                ‖(f (standardPhysicalJetMap U z) : ℂ) -
                  coefficientTorusFourierSum U frequency' coeff' z‖ ≤ η := by
  obtain ⟨A, hA, hsource⟩ := exists_allocated_fixed_positive_fourier m q
  refine ⟨A, hA, ?_⟩
  intro G _ I _ n B _ J _ U b R σ S c x P hP hG hc hL M hperiod
  obtain ⟨d, hd, hdb, hsource⟩ := hsource B U b S c x hP hG hc hL hperiod
  refine ⟨d, hd, hdb, ?_⟩
  intro y _ _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    density cap root dirs F cover ξ
  obtain ⟨f, hfc, hfb, hfi, hfm, hflaw, hf⟩ :=
    hsource y hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨f, hfc, hfb, hfi, hfm, hflaw, ?_⟩
  intro T _ frequency L hL hfrequency
  obtain ⟨rows, hrows, happ⟩ := hf frequency hL hfrequency
  refine ⟨fun a => sitePullbackFrequency standardPhysicalSite (rows a), ?_, ?_⟩
  · intro a j e _ t
    exact standardSiteFrequency_bound (rows a) (hrows a) j e t
  intro coeff η happrox
  refine ⟨retainedSiteCoefficient U root dirs frequency coeff,
    retainedSiteCoefficient_norm_sum U root dirs frequency coeff, ?_⟩
  obtain ⟨a, ha, _, hperiod⟩ := hperiod
  have hdirs : integerScalarLattice (Fin q) (a : ℤ) ≤ dirs.mulVecLin.range :=
    hperiod.trans (integerPeriod_range_le_of_columns (scalarCubeDifferenceMatrix x) dirs Sum.inl
      (fun _ _ => rfl))
  intro z
  exact sampled_density_standard_fourier U root dirs d hd (a : ℤ)
    (by exact_mod_cast ha.ne') hdirs frequency rows coeff f (happ coeff happrox) z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

theorem exists_allocated_jet_fourier_data (m q : ℕ) :
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
      ∀ (_hm : (m : ℝ) ≤ P)
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
        ∃ (Index : Type) (inst : Fintype Index), letI := inst
        ∃ (frequency : Index → ∀ j, (Fin q →₀ ℕ) → J j → ℤ) (coeff : Index → ℂ),
          (∀ a j e, e.degree ≤ j.val + 1 → ∀ t, |(frequency a j e t : ℝ)| ≤ Real.exp Q) ∧
          (∑ a, ‖coeff a‖) ≤ Real.exp Q ∧
          ∀ z : CoefficientTorus (K := Fin q) U,
            ‖(f (standardPhysicalJetMap U z) : ℂ) - coefficientTorusFourierSum U frequency coeff z‖ ≤ δ := by
  obtain ⟨A, hA, hsource⟩ := exists_allocated_uniform_jet_fourier m q
  refine ⟨A, hA, ?_⟩
  intro G _ I _ n B _ J _ U b R σ S c x P hP hG hc hL M hperiod
  obtain ⟨d, hd, hdb, hsource⟩ := hsource B U b S c x hP hG hc hL hperiod
  refine ⟨d, hd, hdb, ?_⟩
  intro y _ _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    density cap root dirs F cover ξ
  obtain ⟨f, hfc, hfb, hfi, hfm, hflaw, hfourier⟩ :=
    hsource y hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨f, hfc, hfb, hfi, hfm, hflaw, ?_⟩
  intro hm hK hRP hσP hcount hI hn hJ hAP hCP hVP δ hδ hδP Q
  obtain ⟨Index, inst, frequency, coeff, _, hfreq, hcoeff, herr⟩ :=
    exists_allocated_coefficient_uniform_fourier B U b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall hP hm hK hRP hσP hcount hI hn hJ
      hAP hL hCP hVP hδ hδP
  let _ := inst
  obtain ⟨frequency', hfreq', hnext⟩ := hfourier frequency (Real.exp_pos _).le hfreq
  obtain ⟨coeff', hcoeff', happ⟩ := hnext coeff (fun z => by rw [norm_sub_rev]; exact herr z)
  have hbudget := allocatedJetFourierBudget_dominates m q A hP
  refine ⟨Index, inst, frequency', coeff', ?_, ?_, happ⟩
  · intro a j e he t
    exact (hfreq' a j e he t).trans hbudget.2.1
  · exact hcoeff'.trans (hcoeff.trans hbudget.2.2)

end Erdos3.VectorPolynomial

end

end OAI
