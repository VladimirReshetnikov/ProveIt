import OAI.Combinatorics.Progressions.Linear.AllocatedFixedKernelCover
import OAI.Combinatorics.Progressions.Linear.FixedKernelEuclideanDensity

namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (o : OrthonormalBasis I ℝ W)

theorem canonicalMixedDensity_continuous_of_ambient
    (c w : I → ℝ) (f : Fin n → ℝ → ℝ) (p : Fin n → PMF ℤ)
    (hf : ∀ i (k : ℤ), f i ((k : ℝ) / basisAxisScale b i) =
      basisAxisScale b i * (p i k).toReal)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 → ∀ d,
      |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1 / 4)
    (hc : Continuous (canonicalAmbientTorusDensity W b o c w f)) :
    Continuous (canonicalMixedDensity W b hb o c w p) := by
  apply (QuotientAddGroup.isQuotientMap_mk
    (latticeSection (standardEuclideanLattice D) W).toAddSubgroup).continuous_iff.mpr
  have hlift : Continuous (fun u : W => fun i => (u.val i : UnitAddCircle)) := by
    apply continuous_pi
    intro i
    exact (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val)
  have he : canonicalMixedDensity W b hb o c w p ∘ QuotientAddGroup.mk =
      fun u : W => canonicalAmbientTorusDensity W b o c w f
        (fun i => (u.val i : UnitAddCircle)) := by
    funext u
    exact (canonicalAmbientTorusDensity_eq W b hb o c w f p hf hs u).symm
  rw [he]
  exact hc.comp hlift

theorem canonicalMixedDensity_continuous
    (c w : I → ℝ) (f : Fin n → ℝ → ℝ) (p : Fin n → PMF ℤ)
    (hf : ∀ i (k : ℤ), f i ((k : ℝ) / basisAxisScale b i) =
      basisAxisScale b i * (p i k).toReal)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 → ∀ d,
      |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1 / 4)
    {M L C V : ℝ≥0}
    (hM : ∀ x, 0 ≤ mixedDensityInterpolation c w f x ∧
      mixedDensityInterpolation c w f x ≤ M)
    (hL : LipschitzWith L (mixedDensityInterpolation c w f))
    (hC : ∀ x, ‖normalizedOrthogonalChart W b x‖ ≤ C * ‖x‖)
    (hV : 0 ≤ mixedDensityCovolumeRatio W b ∧ mixedDensityCovolumeRatio W b ≤ V) :
    Continuous (canonicalMixedDensity W b hb o c w p) :=
  canonicalMixedDensity_continuous_of_ambient W b hb o c w f p hf hs
    (canonicalAmbientTorusDensity_bounds W b o c w f hM hL hC hV).2.continuous

theorem canonicalArrayDensity_continuous {J : Type*} [Fintype J]
    (c w : I → J → ℝ) (f : J → Fin n → ℝ → ℝ) (p : Fin n → J → PMF ℤ)
    (hf : ∀ j i (k : ℤ), f j i ((k : ℝ) / basisAxisScale b i) =
      basisAxisScale b i * (p i j k).toReal)
    (hs : ∀ j x, mixedCoefficientDensity (fun i => c i j) (fun i => w i j)
      (fun i => p i j) x ≠ 0 → ∀ d,
        |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1 / 4)
    (hc : ∀ j, Continuous
      (canonicalAmbientTorusDensity W b o (fun i => c i j) (fun i => w i j) (f j))) :
    Continuous (canonicalArrayDensity W b hb o c w p) := by
  apply continuous_finsetProd
  intro j _
  exact (canonicalMixedDensity_continuous_of_ambient W b hb o _ _ (f j) _
    (hf j) (hs j) (hc j)).comp (continuous_apply j)

end Erdos3

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators

theorem canonicalCoefficientDensity_continuous
    {K : Type*} [Fintype K] {m : ℕ} {J I : Fin m → Type*}
    [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (f : ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) → Fin (n j) → ℝ → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (hf : ∀ j e i (k : ℤ), f j e i ((k : ℝ) / basisAxisScale (b j) i) =
      basisAxisScale (b j) i * (p j i e k).toReal)
    (hs : ∀ j e x, mixedCoefficientDensity (fun i => c j i e) (fun i => w j i e)
      (fun i => p j i e) x ≠ 0 → ∀ d,
        |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
          (orthonormalMixedChart (o j) x) d| ≤ 1 / 4)
    (hc : ∀ j e, Continuous (canonicalAmbientTorusDensity
      (euclideanSubspace (U j)) (b j) (o j) (fun i => c j i e) (fun i => w j i e) (f j e))) :
    Continuous (canonicalCoefficientDensity U b hb o c w p) := by
  apply continuous_finsetProd
  intro j _
  exact (canonicalArrayDensity_continuous _ (b j) (hb j) (o j) (c j) (w j) (f j) (p j)
    (hf j) (hs j) (hc j)).comp
      ((continuous_apply j).comp (euclideanCoefficientEquiv_continuous U))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)

include hC hV hσ1 Cinv hCinv hchart hsmall

theorem allocatedCoefficientDensity_continuous :
    Continuous (allocatedCoefficientDensity B U b hb o hR hσ S) := by
  apply canonicalCoefficientDensity_continuous U b hb o
    (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (fun j e i => allocatedLayerIntegerInterpolation B U b S j i e)
    (allocatedLayerIntegerPMFs B U b hR hσ S)
    (fun j e i => (allocatedLayerIntegerInterpolation_spec B U b S hR hσ j i e).1)
    (allocatedLayerColumns_quarter_support B U b hR hσ S o hσ1 Cinv hCinv hchart hsmall)
  intro j e
  exact (allocatedAmbientFactor_bounds B U b S o C V hC hV hR hσ ⟨j, e⟩).2.continuous

theorem allocatedCoefficientDensity_bounds :
    ∀ x, allocatedCoefficientDensity B U b hb o hR hσ S x ∈
      Set.Icc (0 : ℝ) ((allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)) := by
  intro x
  rw [← allocatedCoefficientAmbientDensity_eq B U b hb o S hR hσ hσ1 Cinv hCinv hchart hsmall x]
  exact (allocatedCoefficientAmbientDensity_bounds B U b o S C V hC hV hR hσ).1 _

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include ν in
theorem allocatedCoefficientDensity_positive_spec :
    Continuous (allocatedCoefficientDensity B U b hb o hR hσ S) ∧
      (∀ x, allocatedCoefficientDensity B U b hb o hR hσ S x ∈
        Set.Icc (0 : ℝ) ((allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
          Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m))) ∧
      Integrable (allocatedCoefficientDensity B U b hb o hR hσ S) μ ∧
      (∫ x, allocatedCoefficientDensity B U b hb o hR hσ S x ∂μ) = 1 ∧
      (allocatedCoefficientSource B U b hR hσ S).map (canonicalCoefficientSample U b hb o) =
        realDensityMeasure μ (allocatedCoefficientDensity B U b hb o hR hσ S) := by
  have h := allocatedCoefficientDensity_spec B U b hb o hR hσ S hσ1 Cinv hCinv hchart hsmall μ ν
  exact ⟨allocatedCoefficientDensity_continuous B U b hb o hR hσ S C V hC hV
      hσ1 Cinv hCinv hchart hsmall,
    allocatedCoefficientDensity_bounds B U b hb o hR hσ S C V hC hV
      hσ1 Cinv hCinv hchart hsmall, h.2.2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped Classical NNReal

theorem exists_allocated_covered_euclidean_density (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧
    ∀ {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (root : LayerSamplerVariables G I n B → ℤ)
    (difference : Fin q → LayerSamplerVariables G I n B → ℤ) {P : ℝ}, 0 ≤ P →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P →
    (∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ Real.exp P) →
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
      ∀ (a : ℤ), a ≠ 0 →
      integerScalarLattice (Fin q) a ≤ (Matrix.of difference).mulVecLin.range →
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
      [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
      [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
      [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
      [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
      [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
      (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
      (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
      (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
      {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
      (S : LayerSamplerScale (G := G) B U b R σ) (C V : Fin m → ℝ≥0)
      (_ : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
      (_ : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
      (_ : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_ : ∀ j, 0 ≤ Cinv j)
      (_ : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
      (_ : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
      (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
      [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
      (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
      [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)],
      let D := allocatedCoefficientDensity B U b hb o hR hσ S
      let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
      let F := euclideanCoefficientJetMap U root (Matrix.of difference)
        (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
      let cover := quotientIntegerCover (coefficientIntegerLattice U) d
      let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))
      ∃ f : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ,
        Continuous f ∧ (∀ z, f z ∈ Set.Icc (0 : ℝ) cap) ∧ Integrable f ξ ∧
        (∫ z, f z ∂ξ) = 1 ∧
        (realDensityMeasure μ (fun x => D (cover x))).map F = realDensityMeasure ξ f ∧
        ∀ {X T : Type*} [Fintype T]
          (frequency : T → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ)
          (c : T → ℂ) {η : ℝ},
          (∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η) →
          ∀ (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j)
            (v : Option (LayerSamplerVariables G I n B) → X → ℝ),
            ‖affineCubeFourierProjection U root difference frequency p c v -
              (f (F (affineCoefficientCoverSample U p hm d v)) : ℂ)‖ ≤ η := by
  obtain ⟨A, hA, hcover⟩ := exists_affine_covered_euclidean_density m q
  refine ⟨A, hA, ?_⟩
  intro G _ I _ n B _ root difference P hP hK hsite
  obtain ⟨d, hd, hdb, hcover⟩ := hcover root difference hP hK hsite
  refine ⟨d, hd, hdb, ?_⟩
  intro a ha hperiod J _ U _ _ _ _ _ _ b hb o R σ hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
  have hs := allocatedCoefficientDensity_positive_spec B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall μ ν
  exact hcover a ha hperiod U μ ν _ hs.1 hs.2.1 hs.2.2.2.1

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)

include hC hV hσ1 hCinv hchart hsmall in
theorem allocatedCoefficientDensity_fixedScale_le_exp
    {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hSP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    allocatedCoefficientDensity B U b hb o hR hσ S x ≤
      Real.exp (allocatedFourierLogBudget m P) := by
  have hcap := (allocatedCoefficientDensity_bounds B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall x).2
  have hbudget := allocatedCoefficient_fourier_input_budget B R σ S.value S.positive C V
    hP hm hK hR hσ hRP hσP hcount hI hn hJ hAP hSP hCP hVP
  exact hcap.trans hbudget.2.2.1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped Classical NNReal

theorem exists_allocated_fixed_positive_density (m q : ℕ) :
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
      ∀ {X T : Type*} [Fintype T]
        (frequency : T → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ)
        (coeff : T → ℂ) {η : ℝ},
        (∀ z, ‖coefficientTorusFourierSum U frequency coeff z - (density z : ℂ)‖ ≤ η) →
        ∀ (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
        (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
        ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : Option (LayerSamplerVariables G I n B) → X → ℝ),
          ‖affineCubeFourierProjection U root dirs frequency p coeff v -
            (f (F (affineCoefficientCoverSample U p hm d v)) : ℂ)‖ ≤ η := by
  obtain ⟨A₀, _, hcover⟩ := exists_fixed_kernel_euclidean_density m q
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
  exact hcover (allocatedPhysicalCubeRoot B U b S c x y) (allocatedPhysicalCubeDirections B U b S x y)
    Sum.inl (fun _ => rfl) (fun _ _ => rfl) U μ ν _ hs.1 hs.2.1 hs.2.2.2.1

end Erdos3.VectorPolynomial

end

end OAI
