import Mathlib.Probability.ProbabilityMassFunction.Integrals
import OAI.Combinatorics.Progressions.Linear.FixedKernelDensityProjection
import OAI.Combinatorics.Progressions.Linear.ShiftedMatrixCountError

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem shiftedSmoothSamples_count_integral (a S : ℝ) (hS : 0 < S) :
    (∫ k : ℤ, smoothProbabilityProfile (((k : ℝ) - a) / S) ∂Measure.count) =
      shiftedSmoothSampleSum a S := by
  have hi := count_integrable_of_zero_off_finset (sampledWeightIndices a S 1)
    (fun k : ℤ => smoothProbabilityProfile (((k : ℝ) - a) / S))
    (sampledWeight_zero_off_indices smoothProbabilityProfile hS smoothProbabilityProfile_zero_outside)
  simpa only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul,
    shiftedSmoothSampleSum] using integral_countable hi

theorem shiftedSmoothSamples_center_l1 (a b S : ℝ) (hS : 1 ≤ S) :
    (∫ k : ℤ, |smoothProbabilityProfile (((k : ℝ) - a) / S) -
      smoothProbabilityProfile (((k : ℝ) - b) / S)| ∂Measure.count) ≤
      6 * S * ((probabilityProfileLipschitz : ℝ) * (|a - b| / S)) := by
  classical
  have hS0 : 0 < S := zero_lt_one.trans_le hS
  let U := sampledWeightIndices a S 1 ∪ sampledWeightIndices b S 1
  have ha (k : ℤ) (hk : k ∉ U) : smoothProbabilityProfile (((k : ℝ) - a) / S) = 0 :=
    sampledWeight_zero_off_indices smoothProbabilityProfile hS0 smoothProbabilityProfile_zero_outside
      k (fun h => hk (Finset.mem_union_left _ h))
  have hb (k : ℤ) (hk : k ∉ U) : smoothProbabilityProfile (((k : ℝ) - b) / S) = 0 :=
    sampledWeight_zero_off_indices smoothProbabilityProfile hS0 smoothProbabilityProfile_zero_outside
      k (fun h => hk (Finset.mem_union_right _ h))
  have hc : (U.card : ℝ) ≤ 6 * S := by
    have hu : (U.card : ℝ) ≤ (sampledWeightIndices a S 1).card +
        ((sampledWeightIndices b S 1).card : ℝ) := by
      exact_mod_cast Finset.card_union_le (sampledWeightIndices a S 1) (sampledWeightIndices b S 1)
    have hca := sampledWeightIndices_card_le a S 1 hS0.le zero_le_one
    have hcb := sampledWeightIndices_card_le b S 1 hS0.le zero_le_one
    linarith
  have he (k : ℤ) : |smoothProbabilityProfile (((k : ℝ) - a) / S) -
      smoothProbabilityProfile (((k : ℝ) - b) / S)| ≤
      (probabilityProfileLipschitz : ℝ) * (|a - b| / S) := by
    have h := smoothProbabilityProfile_lipschitz.norm_sub_le
      (((k : ℝ) - a) / S) (((k : ℝ) - b) / S)
    have hid : ((k : ℝ) - a) / S - ((k : ℝ) - b) / S = (b - a) / S := by ring
    simpa only [Real.norm_eq_abs, hid, abs_div, abs_of_pos hS0, abs_sub_comm b a] using h
  exact (count_density_l1_le_card U _ _ ha hb (fun k _ => he k)).trans
    (mul_le_mul_of_nonneg_right hc (by positivity))

theorem shiftedSmoothCoefficientPMF_center_l1 (a b S : ℝ) (hS : 0 < S)
    (hZa : 0 < shiftedSmoothSampleSum a S) (hZb : 0 < shiftedSmoothSampleSum b S)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ S) :
    (∫ k : ℤ, |(shiftedSmoothCoefficientPMF a S hS hZa k).toReal -
      (shiftedSmoothCoefficientPMF b S hS hZb k).toReal| ∂Measure.count) ≤
      24 * (probabilityProfileLipschitz : ℝ) * |a - b| / S := by
  have hS1 : 1 ≤ S := by linarith [probabilityProfileLipschitz_one_le]
  have hi (c : ℝ) := count_integrable_of_zero_off_finset (sampledWeightIndices c S 1)
    (fun k : ℤ => smoothProbabilityProfile (((k : ℝ) - c) / S))
    (sampledWeight_zero_off_indices smoothProbabilityProfile hS smoothProbabilityProfile_zero_outside)
  have h := normalized_density_l1 Measure.count _ _ (hi a) (hi b)
    (fun _ => (smoothProbabilityProfile_range _).1)
    (by rw [shiftedSmoothSamples_count_integral a S hS]; exact hZa)
    (by rw [shiftedSmoothSamples_count_integral b S hS]; exact hZb)
  rw [shiftedSmoothSamples_count_integral a S hS, shiftedSmoothSamples_count_integral b S hS] at h
  simp only [shiftedSmoothCoefficientPMF_apply]
  apply h.trans
  have hr : S / shiftedSmoothSampleSum a S ≤ 2 :=
    (div_le_iff₀ hZa).mpr (by linarith [(shiftedSmoothSampleSum_bounds a hlarge).1])
  calc
    _ ≤ 2 * (6 * S * ((probabilityProfileLipschitz : ℝ) * (|a - b| / S))) /
        shiftedSmoothSampleSum a S :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (shiftedSmoothSamples_center_l1 a b S hS1) (by norm_num)) hZa.le
    _ = 12 * (S / shiftedSmoothSampleSum a S) *
        ((probabilityProfileLipschitz : ℝ) * (|a - b| / S)) := by ring
    _ ≤ 12 * 2 * ((probabilityProfileLipschitz : ℝ) * (|a - b| / S)) := by
      gcongr
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {X Y : Type*} [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [Countable Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

theorem pmf_image_complex_sum_eq_count_integral (p : PMF X) (f : X → Y)
    (φ : Y → ℂ) {B : ℝ} (hb : ∀ y, ‖φ y‖ ≤ B) :
    (∑' x, ((p x).toReal : ℂ) * φ (f x)) =
      ∫ y, (((p.map f) y).toReal : ℂ) * φ y ∂Measure.count := by
  have hi : Integrable (fun x => φ (f x)) p.toMeasure :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable B
      (ae_of_all _ (fun x => hb (f x)))
  calc
    _ = ∫ x, φ (f x) ∂p.toMeasure := by
      simpa only [Complex.real_smul] using (p.integral_eq_tsum (fun x => φ (f x)) hi).symm
    _ = ∫ y, φ y ∂(p.map f).toMeasure := by
      rw [← PMF.toMeasure_map f p (measurable_of_countable f)]
      exact (integral_map (measurable_of_countable f).aemeasurable
        (measurable_of_countable φ).aestronglyMeasurable).symm
    _ = _ := by
      rw [pmf_realDensity_count]
      exact realDensityMeasure_integral_complex Measure.count _ (measurable_of_countable _)
        (fun _ => ENNReal.toReal_nonneg) φ

theorem pmf_image_count_test_error (p : PMF X) (f : X → Y) (g : Y → ℝ)
    (hg : Integrable g Measure.count) {ε B : ℝ} (hB : 0 ≤ B)
    (he : (∫ y, |((p.map f) y).toReal - g y| ∂Measure.count) ≤ ε)
    (φ : Y → ℂ) (hb : ∀ y, ‖φ y‖ ≤ B) :
    ‖(∑' x, ((p x).toReal : ℂ) * φ (f x)) -
      ∫ y, (g y : ℂ) * φ y ∂Measure.count‖ ≤ B * ε := by
  rw [pmf_image_complex_sum_eq_count_integral p f φ hb]
  exact (density_bounded_complex_test_error Measure.count _ _ (pmf_real_integrable (p.map f)) hg
    φ (measurable_of_countable φ) hb).trans (mul_le_mul_of_nonneg_left he hB)

theorem pmf_projected_count_test_error (p : PMF X) (f : X → Y) (g : Y → ℝ)
    (hg : Integrable g Measure.count) (F : X → ℂ) (φ : Y → ℂ)
    {δ ε B Z : ℝ} (hB : 0 ≤ B) (hZ : 0 < Z) (hb : ∀ y, ‖φ y‖ ≤ B)
    (hprojection : ‖(∑' x, ((p x).toReal : ℂ) * F x) -
      ∑' x, ((p x).toReal : ℂ) * φ (f x)‖ ≤ δ)
    (he : (∫ y, |((p.map f) y).toReal - g y| ∂Measure.count) ≤ ε) :
    ‖(∑' x, ((p x).toReal : ℂ) * F x) / (Z : ℂ) -
      (∫ y, (g y : ℂ) * φ y ∂Measure.count) / (Z : ℂ)‖ ≤ (δ + B * ε) / Z := by
  have ht := pmf_image_count_test_error p f g hg hB he φ hb
  have h := (norm_sub_le_norm_sub_add_norm_sub (∑' x, ((p x).toReal : ℂ) * F x)
    (∑' x, ((p x).toReal : ℂ) * φ (f x))
    (∫ y, (g y : ℂ) * φ y ∂Measure.count)).trans (add_le_add hprojection ht)
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
  exact div_le_div_of_nonneg_right h hZ.le

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem shiftedSmoothProductMass_pos_of_large {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i) :
    0 < shiftedSmoothProductMass a S := by
  rw [shiftedSmoothProductMass_eq_prod a S (fun i => smoothSamplingScale_pos (hS i))]
  exact Finset.prod_pos (fun i _ => shiftedSmoothSampleSum_pos (a i) (hS i))

theorem shiftedSmoothProductPMF_zero {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass 0 S) :
    shiftedSmoothProductPMF 0 S hS hZ = smoothProductPMF S hS := by
  have hz (z : I → ℤ) : rectangularLatticePoint 0 S z = fun i => (z i : ℝ) / S i := by
    funext i
    change ((z i : ℝ) - 0) / S i = (z i : ℝ) / S i
    rw [sub_zero]
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [shiftedSmoothProductPMF_toReal, smoothProductPMF, realWeightPMF_apply,
    shiftedSmoothProductMass, rectangularWeight, hz]

theorem shiftedSmoothProductPMF_center_l1 {I : Type*} [Fintype I]
    (a b S : I → ℝ) (hS : ∀ i, 0 < S i)
    (hZa : 0 < shiftedSmoothProductMass a S) (hZb : 0 < shiftedSmoothProductMass b S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i) :
    (∫ z, |(shiftedSmoothProductPMF a S hS hZa z).toReal -
      (shiftedSmoothProductPMF b S hS hZb z).toReal| ∂Measure.count) ≤
      24 * (probabilityProfileLipschitz : ℝ) * ∑ i, |a i - b i| / S i := by
  classical
  let pa := fun i => shiftedSmoothCoefficientPMF (a i) (S i) (hS i)
    (shiftedSmoothProductMass_coordinate_pos a S hS hZa i)
  let pb := fun i => shiftedSmoothCoefficientPMF (b i) (S i) (hS i)
    (shiftedSmoothProductMass_coordinate_pos b S hS hZb i)
  have h := tensor_density_l1_le_sum (fun _ : I => (Measure.count : Measure ℤ))
    (fun i k => (pa i k).toReal) (fun i k => (pb i k).toReal)
    (fun i => pmf_real_integrable (pa i)) (fun i => pmf_real_integrable (pb i))
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => ENNReal.toReal_nonneg)
    (fun i => pmf_real_integral_count (pa i)) (fun i => pmf_real_integral_count (pb i))
  rw [pi_count_measure] at h
  simp only [shiftedSmoothProductPMF_eq_independent, independentProductPMF_toReal]
  apply h.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_div_assoc] using shiftedSmoothCoefficientPMF_center_l1 (a i) (b i) (S i)
    (hS i) (shiftedSmoothProductMass_coordinate_pos a S hS hZa i)
    (shiftedSmoothProductMass_coordinate_pos b S hS hZb i) (hlarge i)

theorem shiftedSmoothProductPMF_center_test {I : Type*} [Fintype I]
    (a b S : I → ℝ) (hS : ∀ i, 0 < S i)
    (hZa : 0 < shiftedSmoothProductMass a S) (hZb : 0 < shiftedSmoothProductMass b S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (φ : (I → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((shiftedSmoothProductPMF a S hS hZa z).toReal : ℂ) * φ z) -
      ∑' z, ((shiftedSmoothProductPMF b S hS hZb z).toReal : ℂ) * φ z‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ i, |a i - b i| / S i) := by
  have h := pmf_image_count_test_error (shiftedSmoothProductPMF a S hS hZa) id
    (fun z => (shiftedSmoothProductPMF b S hS hZb z).toReal)
    (pmf_real_integrable _) hB
    (by simpa only [PMF.map_id] using shiftedSmoothProductPMF_center_l1 a b S hS hZa hZb hlarge) φ hφ
  have hq := pmf_image_complex_sum_eq_count_integral (shiftedSmoothProductPMF b S hS hZb) id φ hφ
  simp only [id_eq, PMF.map_id] at h hq
  rwa [← hq] at h

theorem shiftedSmoothProductPMF_recenter_test {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZa : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (φ : (I → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ B) :
    ‖(∑' z, ((shiftedSmoothProductPMF a S hS hZa z).toReal : ℂ) * φ z) -
      ∑' z, ((smoothProductPMF S hS z).toReal : ℂ) * φ z‖ ≤
      B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ i, |a i| / S i) := by
  have hZb := shiftedSmoothProductMass_pos_of_large (0 : I → ℝ) S hlarge
  have h := shiftedSmoothProductPMF_center_test a 0 S hS hZa hZb hlarge φ hB hφ
  simpa only [shiftedSmoothProductPMF_zero, Pi.zero_apply, sub_zero] using h

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

theorem selectedResidue_covered_reconstruction_comparison
    {I K F : Type*} [Fintype I] [Fintype K] [Fintype F] {m q : ℕ}
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
    {Y : Type*} [Countable Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (index : (Option K × I → ℤ) → Y) (reconstruct : Y → I → (Unit ⊕ Fin q) → ℤ)
    (houtput : ∀ z, reconstruct (index z) = physicalCubeRootDifferences root (Matrix.of difference) base z)
    (proxy : Y → ℝ) (hg : Integrable proxy Measure.count)
    {η δ ε Z : ℝ} (hη : 0 ≤ η) (hZnorm : 0 < Z)
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
    (himage : (∫ v, |(((selectedResidueSmoothPMF modulus T V hV hZ).map index) v).toReal - proxy v|
        ∂Measure.count) ≤ ε) :
    ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight 0 (fun s => affineSite root difference s)
          (fun s x => test s ((fun i => (base i : ℝ)) + x)) (fun k i => (z (k, i) : ℝ)) *
          (density z : ℂ))) / (Z : ℂ) -
      (∫ v, (proxy v : ℂ) * physicalCubeCoveredTest U root difference D p hm frequency b c test (reconstruct v)
        ∂Measure.count) / (Z : ℂ)‖ ≤ (η + δ + (∑ a, ‖c a‖) * ε) / Z := by
  let law := selectedResidueSmoothPMF modulus T V hV hZ
  let w := fun z : Option K × I → ℤ => layeredSiteWeight 0 (fun s => affineSite root difference s)
    (fun s x => test s ((fun i => (base i : ℝ)) + x)) (fun k i => (z (k, i) : ℝ))
  let φ := physicalCubeCoveredTest U root difference D p hm frequency b c test
  let output := physicalCubeRootDifferences root (Matrix.of difference) base
  have hprojected : ‖(∑' z, ((law z).toReal : ℂ) * (w z * (density z : ℂ))) -
      ∑' z, ((law z).toReal : ℂ) * φ (output z)‖ ≤ η + δ :=
    selectedResidue_density_projection_error U root difference D p hm frequency b c test htest
      base modulus T V hV hZ density hη happrox hprojection
  have hindexed : ‖(∑' z, ((law z).toReal : ℂ) * (w z * (density z : ℂ))) -
      ∑' z, ((law z).toReal : ℂ) * φ (reconstruct (index z))‖ ≤ η + δ := by
    simpa only [houtput] using hprojected
  exact pmf_projected_count_test_error law index proxy hg (fun z => w z * (density z : ℂ))
    (fun y => φ (reconstruct y))
    (Finset.sum_nonneg (fun a _ => norm_nonneg (c a))) hZnorm
    (fun y => physicalCubeCoveredTest_norm_le U root difference D p hm frequency b c test htest (reconstruct y))
    hindexed himage

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

variable {K X : Type*} [Fintype K] [Fintype X]
variable {I : X → Type*} [∀ x, Fintype (I x)]

theorem shiftedSmoothProductPMF_matrix_image (a S : K × X → ℝ)
    (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (M : ∀ x, Matrix (I x) K ℤ) :
    (shiftedSmoothProductPMF a S hS hZ).map (fun z x => M x *ᵥ (fun k => z (k, x))) =
      dependentProductPMF (fun x =>
        (shiftedSmoothProductPMF (fun k => a (k, x)) (fun k => S (k, x))
          (fun k => hS (k, x)) (shiftedSmoothProductMass_slice_pos a S hS hZ x)).map
            (fun z => M x *ᵥ z)) := by
  have hm : (fun z x => M x *ᵥ (fun k => z (k, x))) =
      (fun z x => M x *ᵥ z x) ∘ spatialCoordinateArrayEquiv K X := rfl
  rw [hm, ← PMF.map_comp, shiftedSmoothProductPMF_grouped,
    dependentProductPMF_map]

variable [DecidableEq K] [∀ x, DecidableEq (I x)]

theorem shiftedProductImage_count_error (M : ∀ x, Matrix (I x) K ℤ) (s : ∀ x, I x ↪ K)
    (hM : ∀ x, ((M x).submatrix id (s x)).det ≠ 0)
    (a S : K × X → ℝ) (P : ∀ x, I x → ℝ)
    (hS : ∀ z, 0 < S z) (hP : ∀ x i, 0 < P x i) (hP1 : ∀ x i, 1 ≤ P x i)
    (ha : ∀ z, |a z| ≤ S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (hentry : ∀ x i k, |normalizedIntegerColumns (M x) (fun k => S (k, x)) (P x) i k| ≤ 1)
    (ε : X → ℝ)
    (he : ∀ x v, |(∏ i, P x i) *
        (((shiftedSmoothProductPMF (fun k => a (k, x)) (fun k => S (k, x))
          (fun k => hS (k, x)) (shiftedSmoothProductMass_slice_pos a S hS hZ x)).map
            (fun z => M x *ᵥ z)) v).toReal -
        coefficientImageMask (M x) (P x)
          (selectedCoefficientDensity (M x) (s x) (hM x) (fun k => S (k, x)) (P x)
            (fun k => hS (k, x)) (hP x) (shiftedUnitProfile (fun k => a (k, x)) (fun k => S (k, x)))) v| ≤ ε x)
    (hsmall : (∑ x, shiftedMatrixCountFactor (I x) K * ε x) ≤ 1) :
    (∫ v, |(((shiftedSmoothProductPMF a S hS hZ).map
        (fun z x => M x *ᵥ (fun k => z (k, x)))) v).toReal -
      ∏ x, coefficientGridProxy (M x) (s x) (hM x) (fun k => S (k, x)) (P x)
        (fun k => hS (k, x)) (hP x) (shiftedUnitProfile (fun k => a (k, x)) (fun k => S (k, x))) (v x)|
      ∂Measure.count) ≤ 2 * ∑ x, shiftedMatrixCountFactor (I x) K * ε x := by
  let p := fun x =>
    (shiftedSmoothProductPMF (fun k => a (k, x)) (fun k => S (k, x))
      (fun k => hS (k, x)) (shiftedSmoothProductMass_slice_pos a S hS hZ x)).map (fun z => M x *ᵥ z)
  let g := fun x => coefficientGridProxy (M x) (s x) (hM x) (fun k => S (k, x)) (P x)
    (fun k => hS (k, x)) (hP x) (shiftedUnitProfile (fun k => a (k, x)) (fun k => S (k, x)))
  have hg (x) : Integrable (g x) Measure.count :=
    shiftedMatrixGridProxy_integrable (M x) (s x) (hM x) _ _ (P x)
      (fun k => hS (k, x)) (hP x) (fun k => ha (k, x)) (hentry x)
  have hg0 (x) (v) : 0 ≤ g x v := coefficientGridProxy_nonneg (M x) (s x) (hM x)
    _ _ (fun k => hS (k, x)) (hP x) _ (shiftedUnitProfile_nonneg _ _) v
  have herr (x) : (∫ v, |(p x v).toReal - g x v| ∂Measure.count) ≤ shiftedMatrixCountFactor (I x) K * ε x :=
    shiftedMatrixImage_count_error (M x) (s x) (hM x) _ _ (P x)
      (fun k => hS (k, x)) (hP x) (hP1 x) (fun k => ha (k, x))
      (shiftedSmoothProductMass_slice_pos a S hS hZ x) (hentry x) (he x)
  have h := tensor_density_l1_le_twice_sum (fun x => (Measure.count : Measure (I x → ℤ)))
    (fun x v => (p x v).toReal) g (fun x => pmf_real_integrable (p x)) hg
    (fun _ _ => ENNReal.toReal_nonneg) hg0 (fun x => pmf_real_integral_count (p x))
    (fun x => shiftedMatrixCountFactor (I x) K * ε x) herr hsmall
  rw [pi_count_measure] at h
  simpa only [shiftedSmoothProductPMF_matrix_image, dependentProductPMF_apply, ENNReal.toReal_prod] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

variable {K X : Type*} [Fintype K] [DecidableEq K] [Fintype X]
variable {I : X → Type*} [∀ x, Fintype (I x)] [∀ x, DecidableEq (I x)]

noncomputable def shiftedProductGridProxy (M : ∀ x, Matrix (I x) K ℤ) (s : ∀ x, I x ↪ K)
    (hM : ∀ x, ((M x).submatrix id (s x)).det ≠ 0)
    (a S : K × X → ℝ) (P : ∀ x, I x → ℝ)
    (hS : ∀ z, 0 < S z) (hP : ∀ x i, 0 < P x i) (v : ∀ x, I x → ℤ) : ℝ :=
  ∏ x, coefficientGridProxy (M x) (s x) (hM x) (fun k => S (k, x)) (P x)
    (fun k => hS (k, x)) (hP x) (shiftedUnitProfile (fun k => a (k, x)) (fun k => S (k, x))) (v x)

theorem shiftedProductGridProxy_integrable (M : ∀ x, Matrix (I x) K ℤ) (s : ∀ x, I x ↪ K)
    (hM : ∀ x, ((M x).submatrix id (s x)).det ≠ 0)
    (a S : K × X → ℝ) (P : ∀ x, I x → ℝ)
    (hS : ∀ z, 0 < S z) (hP : ∀ x i, 0 < P x i)
    (ha : ∀ z, |a z| ≤ S z)
    (hentry : ∀ x i k, |normalizedIntegerColumns (M x) (fun k => S (k, x)) (P x) i k| ≤ 1) :
    Integrable (shiftedProductGridProxy M s hM a S P hS hP) Measure.count := by
  rw [← pi_count_measure]
  exact Integrable.fintype_prod_dep (fun x => shiftedMatrixGridProxy_integrable
    (M x) (s x) (hM x) _ _ (P x) (fun k => hS (k, x)) (hP x)
      (fun k => ha (k, x)) (hentry x))

theorem shiftedProduct_test_error (M : ∀ x, Matrix (I x) K ℤ) (s : ∀ x, I x ↪ K)
    (hM : ∀ x, ((M x).submatrix id (s x)).det ≠ 0)
    (a S : K × X → ℝ) (P : ∀ x, I x → ℝ)
    (hS : ∀ z, 0 < S z) (hP : ∀ x i, 0 < P x i) (hP1 : ∀ x i, 1 ≤ P x i)
    (ha : ∀ z, |a z| ≤ S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (hentry : ∀ x i k, |normalizedIntegerColumns (M x) (fun k => S (k, x)) (P x) i k| ≤ 1)
    (ε : X → ℝ)
    (he : ∀ x v, |(∏ i, P x i) *
        (((shiftedSmoothProductPMF (fun k => a (k, x)) (fun k => S (k, x))
          (fun k => hS (k, x)) (shiftedSmoothProductMass_slice_pos a S hS hZ x)).map
            (fun z => M x *ᵥ z)) v).toReal -
        coefficientImageMask (M x) (P x)
          (selectedCoefficientDensity (M x) (s x) (hM x) (fun k => S (k, x)) (P x)
            (fun k => hS (k, x)) (hP x) (shiftedUnitProfile (fun k => a (k, x)) (fun k => S (k, x)))) v| ≤ ε x)
    (hsmall : (∑ x, shiftedMatrixCountFactor (I x) K * ε x) ≤ 1)
    (φ : (∀ x, I x → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ v, ‖φ v‖ ≤ B) :
    ‖(∑' z, ((shiftedSmoothProductPMF a S hS hZ z).toReal : ℂ) *
      φ (fun x => M x *ᵥ (fun k => z (k, x)))) -
      ∫ v, (shiftedProductGridProxy M s hM a S P hS hP v : ℂ) * φ v ∂Measure.count‖ ≤
      B * (2 * ∑ x, shiftedMatrixCountFactor (I x) K * ε x) := by
  exact pmf_image_count_test_error (shiftedSmoothProductPMF a S hS hZ)
    (fun z x => M x *ᵥ (fun k => z (k, x))) _
    (shiftedProductGridProxy_integrable M s hM a S P hS hP ha hentry) hB
    (shiftedProductImage_count_error M s hM a S P hS hP hP1 ha hZ hentry ε he hsmall) φ hφ

end Erdos3

end

end OAI
