import OAI.Combinatorics.Progressions.Lattices.PhysicalResidueOffsetShift

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory
open scoped BigOperators Matrix

variable {K X α : Type*} [Fintype K] [DecidableEq K] [Fintype X]
  [Fintype α] [DecidableEq α]

theorem selectedResidue_physical_product_test_error
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (s : (Unit ⊕ α) ↪ Option K)
    (hM : ((physicalCubeCoefficient root D).submatrix id s).det ≠ 0)
    (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (T : Finset (ColumnResiduePattern (Option K) X modulus))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V))
    (P : X → (Unit ⊕ α) → ℝ) (hP : ∀ x i, 0 < P x i) (hP1 : ∀ x i, 1 ≤ P x i)
    (ha : ∀ r : T, ∀ z, |residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus z| ≤
      residueProfileWidth modulus V z)
    (hentry : ∀ x i k, |normalizedIntegerColumns (physicalCubeCoefficient root D)
      (fun k => residueProfileWidth modulus V (k, x)) (P x) i k| ≤ 1)
    (ε : T → X → ℝ)
    (he : ∀ (r : T) x v, |(∏ i, P x i) *
      (((shiftedSmoothProductPMF
        (fun k => residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus (k, x))
        (fun k => residueProfileWidth modulus V (k, x))
        (fun k => residueProfileWidth_pos modulus V hmodulus hV (k, x))
        (shiftedSmoothProductMass_slice_pos _ _ (residueProfileWidth_pos modulus V hmodulus hV) (hc r) x)).map
        (fun z => physicalCubeCoefficient root D *ᵥ z)) v).toReal -
      coefficientImageMask (physicalCubeCoefficient root D) (P x)
        (selectedCoefficientDensity (physicalCubeCoefficient root D) s hM
          (fun k => residueProfileWidth modulus V (k, x)) (P x)
          (fun k => residueProfileWidth_pos modulus V hmodulus hV (k, x)) (hP x)
          (shiftedUnitProfile
            (fun k => residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus (k, x))
            (fun k => residueProfileWidth modulus V (k, x)))) v| ≤ ε r x)
    (hsmall : ∀ r, (∑ x, shiftedMatrixCountFactor (Unit ⊕ α) (Option K) * ε r x) ≤ 1)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ v, ‖φ v‖ ≤ B) :
    ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
      φ (physicalCubeRootDifferences root D base z)) -
      ∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) *
        ∫ v, (shiftedProductGridProxy (fun _ : X => physicalCubeCoefficient root D)
          (fun _ => s) (fun _ => hM)
          (residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus)
          (residueProfileWidth modulus V) P (residueProfileWidth_pos modulus V hmodulus hV) hP v : ℂ) *
          φ (physicalResidueReconstruct root D base (boundedColumnResidueRepresentative modulus r.val)
            modulus v) ∂Measure.count‖ ≤
      B * ∑ r : T, selectedResidueCellWeight modulus T V r *
        (2 * ∑ x, shiftedMatrixCountFactor (Unit ⊕ α) (Option K) * ε r x) := by
  apply selectedResidue_physical_index_test_error root D base modulus hmodulus T V hV hZ hc
    (fun r => shiftedProductGridProxy (fun _ : X => physicalCubeCoefficient root D)
      (fun _ => s) (fun _ => hM)
      (residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V) P (residueProfileWidth_pos modulus V hmodulus hV) hP)
    (fun r => shiftedProductGridProxy_integrable _ _ _ _ _ _ _ _ (ha r) hentry)
    (fun r => 2 * ∑ x, shiftedMatrixCountFactor (Unit ⊕ α) (Option K) * ε r x) hB _ φ hφ
  intro r
  exact shiftedProductImage_count_error (fun _ : X => physicalCubeCoefficient root D)
    (fun _ => s) (fun _ => hM) _ _ P (residueProfileWidth_pos modulus V hmodulus hV) hP hP1
    (ha r) (hc r) hentry (ε r) (he r) (hsmall r)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Matrix

theorem selectedResidue_covered_product_comparison
    {I K F : Type*} [Fintype I] [Fintype K] [DecidableEq K] [Fintype F] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ) (c : F → ℂ)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1)
    (base : I → ℤ) (modulus : I → ℕ)
    (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (density : (Option K × I → ℤ) → ℝ)
    {η δ : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ z ∈ rectangularWeightIndices 0 V 1,
      ‖(density z : ℂ) - affineCubeFourierSum frequency
        (fun j => translate (fun i => (base i : ℝ)) (p j)) c (fun k i => (z (k, i) : ℝ))‖ ≤ η)
    (hprojection :
      ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight 0 (fun s => affineSite root difference s)
          (fun s x => test s ((fun i => (base i : ℝ)) + x)) (fun k i => (z (k, i) : ℝ)) *
          affineCubeFourierSum frequency (fun j => translate (fun i => (base i : ℝ)) (p j)) c
            (fun k i => (z (k, i) : ℝ)))) -
        (∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
          (layeredSiteWeight 0 (fun s => affineSite root difference s)
            (fun s x => test s ((fun i => (base i : ℝ)) + x)) (fun k i => (z (k, i) : ℝ)) *
            retainedSiteFourierSum U root difference frequency b c
              (affineCoveredSiteSample U root difference D
                (fun j => translate (fun i => (base i : ℝ)) (p j))
                (fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j))
                (fun k i => (z (k, i) : ℝ)))))‖ ≤ δ)
    (s : (Unit ⊕ (Fin q)) ↪ Option K)
    (hM : ((physicalCubeCoefficient root (Matrix.of difference)).submatrix id s).det ≠ 0)
    (hmodulus : ∀ x, 0 < modulus x)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V))
    (P : I → (Unit ⊕ (Fin q)) → ℝ) (hP : ∀ x i, 0 < P x i) (hP1 : ∀ x i, 1 ≤ P x i)
    (ha : ∀ r : T, ∀ z, |residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus z| ≤
      residueProfileWidth modulus V z)
    (hentry : ∀ x i k, |normalizedIntegerColumns (physicalCubeCoefficient root (Matrix.of difference))
      (fun k => residueProfileWidth modulus V (k, x)) (P x) i k| ≤ 1)
    (ε : T → I → ℝ)
    (he : ∀ (r : T) x v, |(∏ i, P x i) *
      (((shiftedSmoothProductPMF
        (fun k => residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus (k, x))
        (fun k => residueProfileWidth modulus V (k, x))
        (fun k => residueProfileWidth_pos modulus V hmodulus hV (k, x))
        (shiftedSmoothProductMass_slice_pos _ _ (residueProfileWidth_pos modulus V hmodulus hV) (hc r) x)).map
        (fun z => physicalCubeCoefficient root (Matrix.of difference) *ᵥ z)) v).toReal -
      coefficientImageMask (physicalCubeCoefficient root (Matrix.of difference)) (P x)
        (selectedCoefficientDensity (physicalCubeCoefficient root (Matrix.of difference)) s hM
          (fun k => residueProfileWidth modulus V (k, x)) (P x)
          (fun k => residueProfileWidth_pos modulus V hmodulus hV (k, x)) (hP x)
          (shiftedUnitProfile
            (fun k => residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus (k, x))
            (fun k => residueProfileWidth modulus V (k, x)))) v| ≤ ε r x)
    (hsmall : ∀ r, (∑ x, shiftedMatrixCountFactor (Unit ⊕ (Fin q)) (Option K) * ε r x) ≤ 1)
    {Z : ℝ} (hZnorm : 0 < Z) :
    ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
      (physicalCubeSiteTest test (physicalCubeRootDifferences root (Matrix.of difference) base z) *
        (density z : ℂ))) / (Z : ℂ) -
      (∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) *
        ∫ v, (shiftedProductGridProxy (fun _ : I => physicalCubeCoefficient root (Matrix.of difference))
          (fun _ => s) (fun _ => hM)
          (residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus)
          (residueProfileWidth modulus V) P (residueProfileWidth_pos modulus V hmodulus hV) hP v : ℂ) *
          physicalCubeCoveredTest U root difference D p hm frequency b c test
            (physicalResidueReconstruct root (Matrix.of difference) base
              (boundedColumnResidueRepresentative modulus r.val) modulus v) ∂Measure.count) / (Z : ℂ)‖ ≤
      (η + δ + (∑ a, ‖c a‖) * ∑ r : T, selectedResidueCellWeight modulus T V r *
        (2 * ∑ x, shiftedMatrixCountFactor (Unit ⊕ Fin q) (Option K) * ε r x)) / Z := by
  have hfirst := selectedResidue_density_projection_error U root difference D p hm frequency b c test htest
    base modulus T V hV hZ density hη happrox hprojection
  simp only [layeredSiteWeight_physicalCube] at hfirst
  have hsecond := selectedResidue_physical_product_test_error root (Matrix.of difference) base s hM
    modulus hmodulus T V hV hZ hc P hP hP1 ha hentry ε he hsmall
    (physicalCubeCoveredTest U root difference D p hm frequency b c test)
    (Finset.sum_nonneg (fun a _ => norm_nonneg (c a)))
    (fun v => physicalCubeCoveredTest_norm_le U root difference D p hm frequency b c test htest v)
  have h := (norm_sub_le_norm_sub_add_norm_sub _
    (∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
      physicalCubeCoveredTest U root difference D p hm frequency b c test
        (physicalCubeRootDifferences root (Matrix.of difference) base z)) _).trans (add_le_add hfirst hsecond)
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZnorm]
  exact div_le_div_of_nonneg_right h hZnorm.le

end Erdos3.BooleanCubeKernel

end

end OAI
