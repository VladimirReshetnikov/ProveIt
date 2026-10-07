import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
import OAI.Combinatorics.Progressions.Geometry.CenteredCoefficientDeckChartMeasurable
import OAI.Combinatorics.Progressions.Linear.CoefficientJointAmbientKernelChart
import OAI.Combinatorics.Progressions.Probability.AllocatedJointMaskedDensityComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule

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

theorem allocatedMaskedCoefficientDensity_sample
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) [NeZero q]
    (test : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → ℝ)
    (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hx : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q) :
    allocatedMaskedCoefficientDensity B U b o S q
      (coefficientDeckResidueMask U bW b hb q test)
      (canonicalCoefficientDeckSample U bW b hb o q (NeZero.pos q) x r) =
      test (coefficientSamplerChartResidues q x r) *
        allocatedCoefficientDensity B U b hb o hR hσ S (canonicalCoefficientSample U b hb o x) := by
  classical
  choose w hw using fun j e => integerResidueMap_surjective (E j) q (r j e)
  have hr : (fun j e => integerResidueMap (E j) q (w j e)) = r := by
    funext j e
    exact hw j e
  rw [← hr]
  rw [allocatedMaskedCoefficientDensity_local B U b o S q (NeZero.pos q) _ _ _ hx _
    (canonicalCoefficientDeckSample_ambient_integer_chart U bW b hb o q (NeZero.pos q) x w),
    coefficientDeckResidueMask_integer_chart]
  congr 1
  rw [← allocatedCoefficientJointAmbientKernel_density B U b hb o S hR hσ hσ1
    Cinv hCinv hchart hsmall, coefficientAmbientTorus_canonicalSample]
  exact (smallBoxTorusKernel_local _ (allocatedCoefficientJointAmbientKernel_support B U b S o) _ hx).symm

theorem allocatedMaskedCoefficientDensity_sample_event
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) [NeZero q]
    (event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop)
    [DecidablePred event]
    (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hx : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q) :
    allocatedMaskedCoefficientDensity B U b o S q
      (coefficientDeckResidueMask U bW b hb q (fun a => if event a then 1 else 0))
      (canonicalCoefficientDeckSample U bW b hb o q (NeZero.pos q) x r) =
      allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice U) q
          (canonicalCoefficientDeckSample U bW b hb o q (NeZero.pos q) x r)) *
        (if event (coefficientSamplerChartResidues q x r) then 1 else 0) := by
  rw [canonicalCoefficientDeckSample_projection]
  rw [allocatedMaskedCoefficientDensity_sample B U bW b hb o S hR hσ hσ1 Cinv hCinv
    hchart hsmall q _ x hx r]
  exact mul_comm _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical NNReal

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
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)

include hσ1 Cinv hCinv hchart hsmall in
theorem allocatedMaskedCoefficientDensity_event_of_nonzero
    (q : ℕ) [NeZero q]
    (event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop)
    (y : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (hy : allocatedCoefficientDensity B U b hb o hR hσ S
      (quotientIntegerCover (coefficientIntegerLattice U) q y) ≠ 0) :
    allocatedMaskedCoefficientDensity B U b o S q
      (coefficientDeckResidueMask U bW b hb q (fun a => if event a then 1 else 0)) y =
      allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice U) q y) *
        (if coefficientDeckChartEvent U bW b hb o q event y then 1 else 0) := by
  obtain ⟨z, hz, _⟩ := canonicalCoefficientDeckSample_recover_nonzero U bW b hb o
    (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (allocatedLayerIntegerPMFs B U b hR hσ S) q (NeZero.pos q) y hy
  have hx : ∀ a, |coefficientSamplerAmbientPoint U b o z.1 a| < 1/2 := by
    intro a
    exact (hz.2 a.1.1).1 a.1.2 a.2
  rw [← hz.1, allocatedMaskedCoefficientDensity_sample_event B U bW b hb o S hR hσ hσ1
    Cinv hCinv hchart hsmall q event z.1 hx z.2,
    coefficientDeckChartEvent_sample_iff U bW b hb o q event z.1 hx z.2]

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV hσ1 Cinv hCinv hchart hsmall in

theorem allocatedMaskedCoefficientDensity_event
    (q : ℕ) [NeZero q]
    (event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop)
    (y : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    allocatedCoefficientDensity B U b hb o hR hσ S
      (quotientIntegerCover (coefficientIntegerLattice U) q y) *
      (if coefficientDeckChartEvent U bW b hb o q event y then 1 else 0) =
    allocatedMaskedCoefficientDensity B U b o S q
      (coefficientDeckResidueMask U bW b hb q (fun a => if event a then 1 else 0)) y := by
  by_cases hy : allocatedCoefficientDensity B U b hb o hR hσ S
      (quotientIntegerCover (coefficientIntegerLattice U) q y) = 0
  · have hmask : ∀ a, coefficientDeckResidueMask U bW b hb q
        (fun a => if event a then 1 else 0) a ∈ Set.Icc (0 : ℝ) 1 := by
      intro a
      simp only [coefficientDeckResidueMask]
      split_ifs <;> constructor <;> norm_num
    have hd := allocatedMaskedCoefficientDensity_le_density B U b o S C V hC hV hb
      hR hσ hσ1 Cinv hCinv hchart hsmall q _ hmask y
    rw [hy] at hd
    rw [hy, zero_mul]
    exact (le_antisymm hd.2 hd.1).symm
  · exact (allocatedMaskedCoefficientDensity_event_of_nonzero B U bW b hb o S hR hσ
      hσ1 Cinv hCinv hchart hsmall q event y hy).symm

include hC hV hσ1 Cinv hCinv hchart hsmall in

theorem allocatedMaskedCoefficientDensity_affine_event
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) [NeZero q]
    (event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop)
    (a : Option (LayerSamplerVariables G I n B) → X → ℝ) :
    allocatedCoefficientDensity B U b hb o hR hσ S (affineSampleCoefficientTorus U p hm a) *
      (if coefficientDeckChartEvent U bW b hb o q event
        (affineCoefficientCoverSample U p hm q a) then 1 else 0) =
    allocatedMaskedCoefficientDensity B U b o S q
      (coefficientDeckResidueMask U bW b hb q (fun r => if event r then 1 else 0))
      (affineCoefficientCoverSample U p hm q a) := by
  simpa only [affineCoefficientCoverSample_projection U p hm q (NeZero.pos q)] using
    allocatedMaskedCoefficientDensity_event B U bW b hb o S hR hσ hσ1 Cinv hCinv
      hchart hsmall C V hC hV q event (affineCoefficientCoverSample U p hm q a)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

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

theorem allocatedMaskedCoefficientDensity_sample_ae
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (q : ℕ) [NeZero q]
    (test : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → ℝ) :
    ∀ᵐ z ∂(allocatedCoefficientSource B U b hR hσ S).prod
      (PMF.uniformOfFintype (CoefficientDeckResidues
        (K := LayerSamplerVariables G I n B) E q)).toMeasure,
      allocatedMaskedCoefficientDensity B U b o S q
          (coefficientDeckResidueMask U bW b hb q test)
          (canonicalCoefficientDeckSample U bW b hb o q (NeZero.pos q) z.1 z.2) =
        test (coefficientSamplerChartResidues q z.1 z.2) *
          allocatedCoefficientDensity B U b hb o hR hσ S
            (quotientIntegerCover (coefficientIntegerLattice U) q
              (canonicalCoefficientDeckSample U bW b hb o q (NeZero.pos q) z.1 z.2)) := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (allocatedCoefficientSource_ambient_small B U b o hR hσ S hσ1 Cinv hCinv
      hchart hsmall)] with z hz
  rw [canonicalCoefficientDeckSample_projection]
  exact allocatedMaskedCoefficientDensity_sample B U bW b hb o S hR hσ hσ1
    Cinv hCinv hchart hsmall q test z.1 hz z.2

end Erdos3.VectorPolynomial

end

end OAI
