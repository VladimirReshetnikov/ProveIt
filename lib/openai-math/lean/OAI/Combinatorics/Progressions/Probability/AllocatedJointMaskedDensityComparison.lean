import OAI.Combinatorics.Progressions.Estimates.CoefficientPairCover
import OAI.Combinatorics.Progressions.Lattices.SelectedResidueRefinementMean

namespace OAI

section

namespace Erdos3
open MeasureTheory

noncomputable def dominatedDensityRatio {X : Type*} (D A : X → ℝ) (x : X) : ℂ :=
  (A x / D x : ℝ)

theorem dominatedDensityRatio_mul {X : Type*} (D A : X → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hAD : ∀ x, A x ≤ D x) (x : X) :
    (D x : ℂ) * dominatedDensityRatio D A x = (A x : ℂ) := by
  by_cases hD : D x = 0
  · have hAx : A x = 0 := le_antisymm (by simpa [hD] using hAD x) (hA x)
    simp [dominatedDensityRatio, hD, hAx]
  · simp only [dominatedDensityRatio, Complex.ofReal_div]
    field_simp [hD]

theorem dominatedDensityRatio_nonneg {X : Type*} (D A : X → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hAD : ∀ x, A x ≤ D x) (x : X) :
    0 ≤ (dominatedDensityRatio D A x).re :=
  div_nonneg (hA x) ((hA x).trans (hAD x))

theorem dominatedDensityRatio_norm_le {X : Type*} (D A : X → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hAD : ∀ x, A x ≤ D x) (x : X) :
    ‖dominatedDensityRatio D A x‖ ≤ 1 := by
  have hD0 := (hA x).trans (hAD x)
  rw [dominatedDensityRatio, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hA x) hD0)]
  by_cases hD : D x = 0
  · simp [hD]
  · exact (div_le_one (lt_of_le_of_ne hD0 (Ne.symm hD))).mpr (hAD x)

theorem dominatedDensityRatio_measurable {X : Type*} [MeasurableSpace X]
    (D A : X → ℝ) (hD : Measurable D) (hA : Measurable A) :
    Measurable (dominatedDensityRatio D A) :=
  Complex.measurable_ofReal.comp (hA.div hD)

theorem dominatedDensityRatio_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (D A : X → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hAD : ∀ x, A x ≤ D x) :
    (∫ x, (D x : ℂ) * dominatedDensityRatio D A x ∂μ) =
      ((∫ x, A x ∂μ) : ℂ) := by
  simp_rw [dominatedDensityRatio_mul D A hA hAD]

theorem selectedResidueDensityPMF_maskedMean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D A : (K × I → ℤ) → ℝ) (hA : ∀ x, 0 ≤ A x) (hAD : ∀ x, A x ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) :
    (∑' x, ((selectedResidueDensityPMF modulus G V hV hZ D
      (fun x => (hA x).trans (hAD x)) hD x).toReal : ℂ) * dominatedDensityRatio D A x) =
      (selectedResidueDensityMass modulus G V A : ℂ) /
        (selectedResidueDensityMass modulus G V D : ℂ) := by
  rw [selectedResidueDensityPMF_complexMean]
  simp_rw [dominatedDensityRatio_mul D A hA hAD]
  rw [← selectedResidueDensityMass_complex modulus G V hV hZ]

theorem selectedResidueDensityPMF_maskedMean_error {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D A : (K × I → ℤ) → ℝ) (hA : ∀ x, 0 ≤ A x) (hAD : ∀ x, A x ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    {a E ε : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hlower : 1 / 2 ≤ selectedResidueDensityMass modulus G V D)
    (herror : |selectedResidueDensityMass modulus G V A - a| ≤ E)
    (hmass : |selectedResidueDensityMass modulus G V D - 1| ≤ ε) :
    ‖(∑' x, ((selectedResidueDensityPMF modulus G V hV hZ D
      (fun x => (hA x).trans (hAD x)) hD x).toReal : ℂ) * dominatedDensityRatio D A x) -
      (a : ℂ)‖ ≤ 2 * E + 2 * ε := by
  have hnum : ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
      ((D x : ℂ) * dominatedDensityRatio D A x)) - (a : ℂ)‖ ≤ E := by
    simp_rw [dominatedDensityRatio_mul D A hA hAD]
    rw [← selectedResidueDensityMass_complex modulus G V hV hZ,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact herror
  have hcap : ‖(a : ℂ)‖ ≤ 1 := by simpa [Real.norm_of_nonneg ha.1] using ha.2
  simpa using selectedResidueDensityPMF_error modulus G V hV hZ D
    (fun x => (hA x).trans (hAD x)) hD (dominatedDensityRatio D A)
    hlower hnum hmass hcap

theorem selectedResidueDensityPMF_event_error {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D A : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (event : (K × I → ℤ) → Prop) [DecidablePred event]
    (hmask : ∀ x, D x * (if event x then 1 else 0) = A x)
    {a E ε : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hlower : 1 / 2 ≤ selectedResidueDensityMass modulus G V D)
    (herror : |selectedResidueDensityMass modulus G V A - a| ≤ E)
    (hmass : |selectedResidueDensityMass modulus G V D - 1| ≤ ε) :
    |(∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
      (if event x then 1 else 0)) - a| ≤ 2 * E + 2 * ε := by
  let f : (K × I → ℤ) → ℂ := fun x => if event x then 1 else 0
  have hprod (x) : (D x : ℂ) * f x = (A x : ℂ) := by
    simpa only [f, Complex.ofReal_mul, apply_ite, Complex.ofReal_one, Complex.ofReal_zero]
      using congrArg Complex.ofReal (hmask x)
  have hnum : ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
      ((D x : ℂ) * f x)) - (a : ℂ)‖ ≤ E := by
    simp_rw [hprod]
    rw [← selectedResidueDensityMass_complex modulus G V hV hZ,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact herror
  have hcap : ‖(a : ℂ)‖ ≤ 1 := by simpa [Real.norm_of_nonneg ha.1] using ha.2
  have h := selectedResidueDensityPMF_error modulus G V hV hZ D hD0 hD f hlower hnum hmass hcap
  have hid : (∑' x, ((selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal : ℂ) * f x) =
      ((∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
        (if event x then 1 else 0) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_tsum, Complex.ofReal_mul, apply_ite,
      Complex.ofReal_one, Complex.ofReal_zero, f]
  rw [hid, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  simpa using h

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem maskedDensity_integral_of_sample_law
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure X) (μ : Measure Y) (sample : X → Y) (hsample : Measurable sample)
    (D A : Y → ℝ) (hDm : Measurable D) (hAm : Measurable A)
    (hA0 : ∀ y, 0 ≤ A y) (hAD : ∀ y, A y ≤ D y)
    (hlaw : ρ.map sample = realDensityMeasure μ D)
    (f : X → ℝ) (hmask : ∀ᵐ x ∂ρ, A (sample x) = f x * D (sample x)) :
    (∫ y, A y ∂μ) = ∫ x, f x ∂ρ := by
  have hD0 : ∀ y, 0 ≤ D y := fun y => (hA0 y).trans (hAD y)
  have hDae : ∀ᵐ y ∂realDensityMeasure μ D, D y ≠ 0 :=
    realDensityMeasure_ae_of_support μ D hDm _ (fun y hy => hy)
  rw [← hlaw] at hDae
  have hDs : ∀ᵐ x ∂ρ, D (sample x) ≠ 0 :=
    ae_of_ae_map hsample.aemeasurable hDae
  let φ := dominatedDensityRatio D A
  have hφ : Measurable φ := dominatedDensityRatio_measurable D A hDm hAm
  have hφsample : (fun x => φ (sample x)) =ᵐ[ρ] fun x => (f x : ℂ) := by
    filter_upwards [hDs, hmask] with x hx hAx
    simp only [φ, dominatedDensityRatio, hAx, mul_div_cancel_right₀ _ hx]
  apply Complex.ofReal_injective
  calc
    Complex.ofReal (∫ y, A y ∂μ) = ∫ y, (A y : ℂ) ∂μ := integral_ofReal.symm
    _ = ∫ y, (D y : ℂ) * φ y ∂μ := by
      simp only [φ, dominatedDensityRatio_mul D A hA0 hAD]
    _ = ∫ y, φ y ∂realDensityMeasure μ D :=
      (realDensityMeasure_integral_complex μ D hDm hD0 φ).symm
    _ = ∫ x, φ (sample x) ∂ρ := by
      rw [← hlaw]
      exact integral_map hsample.aemeasurable hφ.aestronglyMeasurable
    _ = ∫ x, (f x : ℂ) ∂ρ := integral_congr_ae hφsample
    _ = Complex.ofReal (∫ x, f x ∂ρ) := integral_ofReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem allocatedMaskedCoefficientDensity_continuous
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (q : ℕ) (mask : (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1) :
    Continuous (allocatedMaskedCoefficientDensity B U b o S q mask) := by
  have hk := allocatedCoefficientJointAmbientKernel_bounds B U b S o C V hC hV hR hσ
  exact (maskedIntegerTorusKernel_lipschitz q mask hmask _ hk.2 (fun x => (hk.1 x).1)
    (allocatedCoefficientJointAmbientKernel_support B U b S o)).continuous.comp
    (coefficientAmbientTorus_continuous U)

include hC hV in
theorem allocatedMaskedCoefficientDensity_le_density
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) (mask : (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    0 ≤ allocatedMaskedCoefficientDensity B U b o S q mask x ∧
      allocatedMaskedCoefficientDensity B U b o S q mask x ≤
        allocatedCoefficientDensity B U b hb o hR hσ S
          (quotientIntegerCover (coefficientIntegerLattice U) q x) := by
  have hk := allocatedCoefficientJointAmbientKernel_bounds B U b S o C V hC hV hR hσ
  have hrange := maskedIntegerTorusKernel_range q mask hmask
    (allocatedCoefficientJointAmbientKernel B U b S o)
    (show 0 ≤ (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) by positivity)
    hk.1 (allocatedCoefficientJointAmbientKernel_support B U b S o) (coefficientAmbientTorus U x)
  refine ⟨hrange.1, ?_⟩
  have hle := maskedIntegerTorusKernel_le q mask (fun r => (hmask r).2)
    (allocatedCoefficientJointAmbientKernel B U b S o) (fun z => (hk.1 z).1)
    (allocatedCoefficientJointAmbientKernel_support B U b S o) (coefficientAmbientTorus U x)
  rw [← coefficientAmbientTorus_cover,
    allocatedCoefficientJointAmbientKernel_density B U b hb o S hR hσ hσ1 Cinv hCinv hchart hsmall] at hle
  exact hle

theorem allocatedMaskedCoefficientDensity_local
    (q : ℕ) (hq : 0 < q)
    (mask : (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (y : CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ℝ)
    (hy : ∀ i, |y i| < 1/2)
    (k : CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ℤ)
    (hx : coefficientAmbientTorus U x =
      fun i => (((y i + (k i : ℝ)) / q : ℝ) : UnitAddCircle)) :
    allocatedMaskedCoefficientDensity B U b o S q mask x =
      mask (fun i => (-k i : ZMod q)) * allocatedCoefficientJointAmbientKernel B U b S o y := by
  rw [allocatedMaskedCoefficientDensity, hx]
  exact maskedIntegerTorusKernel_local q hq mask _
    (allocatedCoefficientJointAmbientKernel_support B U b S o) y hy k

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

noncomputable def allocatedMaskedTiltedConstant (m : ℕ) : ℕ :=
  Classical.choose (exists_affine_coefficient_cover_tilted_family_comparison.{0, 0, 0, 0} m)

theorem allocatedMaskedTiltedConstant_ge_two (m : ℕ) :
    2 ≤ allocatedMaskedTiltedConstant m :=
  (Classical.choose_spec (exists_affine_coefficient_cover_tilted_family_comparison.{0, 0, 0, 0} m)).1

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedMaskedCoefficientDensity_one
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    allocatedMaskedCoefficientDensity B U b o S q (fun _ => 1) x =
      allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice U) q x) := by
  rw [allocatedMaskedCoefficientDensity, maskedIntegerTorusKernel_one,
    ← coefficientAmbientTorus_cover,
    allocatedCoefficientJointAmbientKernel_density B U b hb o S hR hσ hσ1 Cinv hCinv hchart hsmall]

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in

theorem exists_allocated_masked_density_tilted_comparison
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) (hq : 0 < q)
    (mask : (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    {P δ : ℝ} (hP : 0 ≤ P) (hmP : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hqP : (q : ℝ) ≤ Real.exp P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type} [Fintype X] [DecidableEq X]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {Ps ε ρ Rs Smax : ℝ} (hPs : 0 ≤ Ps) (hX : (Fintype.card X : ℝ) ≤ Ps)
    (hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Ps)
    (hqPs : (q : ℝ) ≤ Real.exp Ps)
    (hε : 0 < ε) (hρ : 0 < ρ) (hεPs : 1 / ε ≤ Real.exp Ps) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, (stride x : ℝ) ≤ Smax)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hcells : cells.Nonempty)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hsmallError : 2 * δ + ε ≤ 1 / 2) :
    let D := allocatedCoefficientDensity B U b hb o hR hσ S
    let Dc := fun x => D (quotientIntegerCover (coefficientIntegerLattice U) q x)
    let A := allocatedMaskedCoefficientDensity B U b o S q mask
    let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))
    let Dphysical := fun z => D (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 2 * δ + ε ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      ‖(∑' z, ((selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal : ℂ) *
          dominatedDensityRatio Dc A (sample z)) - ((∫ x, A x ∂μ) : ℂ)‖ ≤ 4 * (2 * δ + ε) := by
  dsimp only
  let D := allocatedCoefficientDensity B U b hb o hR hσ S
  let Dc := fun x => D (quotientIntegerCover (coefficientIntegerLattice U) q x)
  let A := allocatedMaskedCoefficientDensity B U b o S q mask
  let f := dominatedDensityRatio Dc A
  have hpair (a : Bool) := exists_allocated_masked_coefficient_uniform_fourier B U b o S C V hC hV
    hR hσ q (fun r => if a then mask r else 1)
    (by intro r; cases a <;> simp [hmask r]) hP hmP hK hRP hσP hcount hI hn hJ hAP hLP
    hCP hVP hqP hδ hδP
  choose F inst frequency coeff hcard hfreq hmass happ using hpair
  let _ := inst
  have hspec := allocatedCoefficientDensity_spec B U b hb o hR hσ S hσ1 Cinv hCinv hchart hsmall μ ν
  have hDc := coefficientCover_density_integral U μ q hq D hspec.2.2.1 hspec.2.2.2.1
  have hdom := allocatedMaskedCoefficientDensity_le_density B U b o S C V hC hV hb
    hR hσ hσ1 Cinv hCinv hchart hsmall q mask hmask
  have hA0 : ∀ x, 0 ≤ A x := fun x => (hdom x).1
  have hAD : ∀ x, A x ≤ Dc x := fun x => (hdom x).2
  have hone : allocatedMaskedCoefficientDensity B U b o S q (fun _ => 1) = Dc := by
    funext x
    exact allocatedMaskedCoefficientDensity_one B U b hb o S hR hσ hσ1 Cinv hCinv hchart hsmall q x
  have hDccont : Continuous Dc := by
    rw [← hone]
    exact allocatedMaskedCoefficientDensity_continuous B U b o S C V hC hV hR hσ q
      (fun _ => 1) (fun _ => by constructor <;> norm_num)
  have hAcont : Continuous A := allocatedMaskedCoefficientDensity_continuous
    B U b o S C V hC hV hR hσ q mask hmask
  have hf : AEStronglyMeasurable f μ :=
    (dominatedDensityRatio_measurable Dc A hDccont.measurable hAcont.measurable).aestronglyMeasurable
  have happ' (a : Bool) (x) :
      ‖(Dc x : ℂ) * (if a then f x else 1) - coefficientTorusFourierSum U (frequency a) (coeff a) x‖ ≤ δ := by
    cases a
    · simpa only [Bool.false_eq_true, ↓reduceIte, mul_one, hone] using happ false x
    · simpa only [↓reduceIte, f, dominatedDensityRatio_mul Dc A hA0 hAD, A] using happ true x
  have hresult := (Classical.choose_spec (exists_affine_coefficient_cover_tilted_family_comparison.{0, 0, 0, 0} m)).2
    F hPs hX hframe U μ (by positivity) (Real.exp_le_exp.mpr hfreqPs) frequency hfreq coeff
    (by positivity) (Real.exp_le_exp.mpr hmassPs) hmass poly hp hm q hq hqPs stride hstride
    hSmax hSmaxPs hρ hε hρPs hεPs hstrideMax H hsize hrank hRs cells hcells width hwidth hwide
    Dc hDc.1 hDc.2 (fun x => hspec.2.1 _) f hf (dominatedDensityRatio_norm_le Dc A hA0 hAD)
    hδ.le happ' hsmallError
  have hsample : (fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      Dc (affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ)))) =
      (fun z => D (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))) := by
    funext z
    exact coefficientCover_density_sample U poly hm q hq D _
  have hint := dominatedDensityRatio_integral μ Dc A hA0 hAD
  refine ⟨fun z => hspec.2.1 _, ?_⟩
  simpa only [hsample, f, hint, Dc, A, D] using hresult

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in

theorem exists_allocated_joint_masked_density_comparison
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) (hq : 0 < q)
    {P δ : ℝ} (hP : 0 ≤ P) (hmP : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hqP : (q : ℝ) ≤ Real.exp P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type} [Fintype X] [DecidableEq X]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {Ps ε ρ Rs Smax : ℝ} (hPs : 0 ≤ Ps) (hX : (Fintype.card X : ℝ) ≤ Ps)
    (hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Ps)
    (hqPs : (q : ℝ) ≤ Real.exp Ps)
    (hε : 0 < ε) (hρ : 0 < ρ) (hεPs : 1 / ε ≤ Real.exp Ps) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, (stride x : ℝ) ≤ Smax)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hcells : cells.Nonempty)
    (mask : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride →
      (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (hmask : ∀ r z, mask r z ∈ Set.Icc (0 : ℝ) 1)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hsmallError : 2 * δ + ε ≤ 1 / 2) :
    let D := allocatedCoefficientDensity B U b hb o hR hσ S
    let Dc := fun x => D (quotientIntegerCover (coefficientIntegerLattice U) q x)
    let A := fun r => allocatedMaskedCoefficientDensity B U b o S q (mask r)
    let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))
    let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ => D (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 2 * δ + ε ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      ‖(∑' z, ((selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal : ℂ) *
          dominatedDensityRatio Dc (A (columnResiduePattern stride z)) (sample z)) -
        ∑' z, ((selectedResidueSmoothPMF stride cells width hwidth hZ z).toReal : ℂ) *
          ((∫ x, A (columnResiduePattern stride z) x ∂μ) : ℂ)‖ ≤ 12 * (2 * δ + ε) := by
  dsimp only
  let D := allocatedCoefficientDensity B U b hb o hR hσ S
  let Dc := fun x => D (quotientIntegerCover (coefficientIntegerLattice U) q x)
  let A := fun r => allocatedMaskedCoefficientDensity B U b o S q (mask r)
  let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
    affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))
  let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ => D (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
  let φ := fun z => dominatedDensityRatio Dc (A (columnResiduePattern stride z)) (sample z)
  have hlocal (r : cells) := exists_allocated_masked_density_tilted_comparison B U b hb o S C V hC hV
    hR hσ hσ1 Cinv hCinv hchart hsmall q hq (mask r.val) (hmask r.val)
    hP hmP hK hRP hσP hcount hI hn hJ hAP hLP hCP hVP hqP hδ hδP μ ν poly hp hm
    hPs hX hframe hqPs hε hρ hεPs hρPs stride hstride hSmax hSmaxPs hstrideMax
    H hsize hrank hRs {r.val} (Finset.singleton_nonempty _) width hwidth hwide hfreqPs hmassPs hsmallError
  choose hD0r hZr hDr hmassr hlower hupper htestr using hlocal
  have hspec := allocatedCoefficientDensity_spec B U b hb o hR hσ S hσ1 Cinv hCinv hchart hsmall μ ν
  have hD0 : ∀ z, 0 ≤ Dphysical z := fun z => hspec.2.1 _
  have hZ := selectedResidueSmoothWeight_mass_pos_of_singletons stride cells hcells width hwidth hZr
  let w : FiniteProbabilityWeights cells :=
    ⟨selectedResidueCellWeight stride cells width,
      selectedResidueCellWeight_nonneg stride cells width,
      selectedResidueCellWeight_sum stride cells width hwidth hZ⟩
  have hglobalmass : |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 2 * δ + ε := by
    rw [selectedResidueDensityMass_singleton_mixture stride cells width hwidth hZ hZr]
    exact w.abs_mean_sub_const_le _ 1 (2 * δ + ε) hmassr
  have hlo : 1/2 ≤ selectedResidueDensityMass stride cells width Dphysical := by
    have := (abs_le.mp hglobalmass).1
    linarith
  have hhi : selectedResidueDensityMass stride cells width Dphysical ≤ 3/2 := by
    have := (abs_le.mp hglobalmass).2
    linarith
  have hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical := by linarith
  have hdom (r) := allocatedMaskedCoefficientDensity_le_density B U b o S C V hC hV hb
    hR hσ hσ1 Cinv hCinv hchart hsmall q (mask r) (hmask r)
  have hA0 (r) : ∀ x, 0 ≤ A r x := fun x => (hdom r x).1
  have hAD (r) : ∀ x, A r x ≤ Dc x := fun x => (hdom r x).2
  have hφ : ∀ z, ‖φ z‖ ≤ 1 := fun z =>
    dominatedDensityRatio_norm_le Dc (A _) (hA0 _) (hAD _) _
  have hraw (r : cells) :
      ‖(∑' z, ((selectedResidueSmoothPMF stride {r.val} width hwidth (hZr r) z).toReal : ℂ) *
        ((Dphysical z : ℂ) * φ z)) - ((∫ x, A r.val x ∂μ) : ℂ)‖ ≤
      4 * (2 * δ + ε) + (2 * δ + ε) := by
    apply selectedResidueDensityPMF_raw_error stride {r.val} width hwidth (hZr r)
      Dphysical hD0 (hDr r) φ hφ ?_ (hmassr r)
    rw [selectedResidueDensityPMF_singleton_complexMean_congr stride r.val width hwidth (hZr r)
      Dphysical hD0 (hDr r) φ
      (fun z => dominatedDensityRatio Dc (A r.val) (sample z))
      (fun z hz => by simp only [φ, hz])]
    exact htestr r
  have hDc := coefficientCover_density_integral U μ q hq D hspec.2.2.1 hspec.2.2.2.1
  have htarget (r : cells) : ‖((∫ x, A r.val x ∂μ) : ℂ)‖ ≤ 1 := by
    rw [← dominatedDensityRatio_integral μ Dc (A r.val) (hA0 _) (hAD _)]
    exact norm_density_integral_le_one μ Dc hDc.1 (fun x => hspec.2.1 _) hDc.2 _
      (dominatedDensityRatio_norm_le Dc (A _) (hA0 _) (hAD _))
  refine ⟨hD0, hZ, hDpos, hglobalmass, hlo, hhi, ?_⟩
  have he := selectedResidueDensityPMF_singleton_mixture_error stride cells width hwidth hZ hZr
    Dphysical hD0 hDpos φ (fun r => ((∫ x, A r.val x ∂μ) : ℂ))
    hsmallError hraw hmassr htarget
  have htargetMean : (∑' z, ((selectedResidueSmoothPMF stride cells width hwidth hZ z).toReal : ℂ) *
      ((∫ x, A (columnResiduePattern stride z) x ∂μ) : ℂ)) =
      ∑ r : cells, (selectedResidueCellWeight stride cells width r : ℂ) * ((∫ x, A r.val x ∂μ) : ℂ) := by
    rw [selectedResidueSmoothPMF_singleton_mixture stride cells width hwidth hZ hZr]
    apply Finset.sum_congr rfl
    intro r _
    exact congrArg (fun t : ℂ => (selectedResidueCellWeight stride cells width r : ℂ) * t)
      (selectedResidueSmoothPMF_singleton_residue_mean stride r.val width hwidth (hZr r)
        (fun rr => ((∫ x, A rr x ∂μ) : ℂ)))
  rw [htargetMean]
  convert he using 1
  ring

end Erdos3.VectorPolynomial

end

end OAI
