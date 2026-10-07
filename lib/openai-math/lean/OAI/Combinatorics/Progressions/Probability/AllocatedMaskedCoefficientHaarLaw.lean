import OAI.Combinatorics.Progressions.Estimates.AllocatedMaskedCoefficientSampleAE
import OAI.Combinatorics.Progressions.Estimates.CoefficientDeckMaskedIntegral

namespace OAI

section

namespace Erdos3

noncomputable def allocatedUniformPMFCanonical (α : Type*) [Finite α] [Nonempty α] : PMF α :=
  @PMF.uniformOfFintype α (Fintype.ofFinite α) inferInstance

theorem allocatedUniformPMF_fintype_transport (α : Type*) [Fintype α] [Nonempty α] :
    PMF.uniformOfFintype α = allocatedUniformPMFCanonical α := by
  unfold allocatedUniformPMFCanonical
  congr 1
  exact Subsingleton.elim _ _

end Erdos3

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped NNReal Classical
attribute [local irreducible] coefficientDeckKernelEquiv canonicalCoefficientDeckSample
  coefficientSamplerAmbientPoint allocatedMaskedCoefficientDensity
  allocatedCoefficientSource allocatedCoefficientDensity

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)]
variable [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
include hC hV in
theorem allocatedMaskedCoefficientDensity_haar_data
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) [NeZero q]
    (test : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → ℝ)
    (htest : ∀ r, test r ∈ Set.Icc (0 : ℝ) 1) :
    Measurable (allocatedMaskedCoefficientDensity B U b o S q
      (coefficientDeckResidueMask U bW b hb q test)) ∧
    ∀ y, 0 ≤ allocatedMaskedCoefficientDensity B U b o S q
      (coefficientDeckResidueMask U bW b hb q test) y ∧
      allocatedMaskedCoefficientDensity B U b o S q
        (coefficientDeckResidueMask U bW b hb q test) y ≤
      allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice U) q y) := by
  let mask := coefficientDeckResidueMask U bW b hb q test
  have hm : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1 := fun r => htest _
  refine ⟨?_, ?_⟩
  · exact (allocatedMaskedCoefficientDensity_continuous B U b o S C V hC hV hR hσ q mask hm).measurable
  · exact allocatedMaskedCoefficientDensity_le_density B U b o S C V hC hV hb hR hσ hσ1
      Cinv hCinv hchart hsmall q mask hm

include hC hV ν in
theorem allocatedMaskedCoefficientDensity_haar_integral
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) [NeZero q]
    (test : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → ℝ)
    (htest : ∀ r, test r ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y, allocatedMaskedCoefficientDensity B U b o S q
      (coefficientDeckResidueMask U bW b hb q test) y ∂μ) =
    ∫ p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
        CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q,
      test (coefficientSamplerChartResidues q p.1 p.2)
      ∂(allocatedCoefficientSource B U b hR hσ S).prod
        (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).toMeasure := by
  have hdata := allocatedMaskedCoefficientDensity_haar_data B U bW b hb o S C V hC hV
    hR hσ hσ1 Cinv hCinv hchart hsmall q test htest
  have hdm := (allocatedCoefficientDensity_spec B U b hb o hR hσ S hσ1
    Cinv hCinv hchart hsmall μ ν).1
  have hlaw := allocatedCoefficientDeckSample_density_law B U b hR hσ S E hb o bW q μ ν
    hσ1 Cinv hCinv hchart hsmall
  have hae := allocatedMaskedCoefficientDensity_sample_ae B U bW b hb o S hR hσ hσ1
    Cinv hCinv hchart hsmall q test
  have hresult := CoefficientDeckDensityLaw.masked_integral (K := LayerSamplerVariables G I n B)
    U bW b hb o μ (allocatedCoefficientSource B U b hR hσ S)
    (allocatedCoefficientDensity B U b hb o hR hσ S) q hlaw hdm
    (allocatedMaskedCoefficientDensity B U b o S q (coefficientDeckResidueMask U bW b hb q test))
    hdata.1 (fun y => (hdata.2 y).1) (fun y => (hdata.2 y).2)
    (fun p => test (coefficientSamplerChartResidues q p.1 p.2))
    (by simpa only [allocatedUniformPMF_fintype_transport] using hae)
  simpa only [allocatedUniformPMF_fintype_transport] using hresult

end Erdos3.VectorPolynomial

end

end OAI
