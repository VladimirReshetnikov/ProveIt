import OAI.Combinatorics.Progressions.Probability.SelectedSingletonSmoothIndexLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem normalizedRealQuadrature_error {A M T E F : ℝ}
    (hM : 1 / 2 ≤ M) (hA : |A - T| ≤ E) (hm : |M - 1| ≤ F)
    (hT : |T| ≤ 1) : |A / M - T| ≤ 2 * (E + F) := by
  have hMp : 0 < M := by linarith
  have hF : 0 ≤ F := (abs_nonneg _).trans hm
  have hE : 0 ≤ E := (abs_nonneg _).trans hA
  have he : A / M - T = ((A - T) + T * (1 - M)) / M := by
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hMp]
  apply (div_le_iff₀ hMp).mpr
  calc
    _ ≤ |A - T| + |T| * |1 - M| := by
      simpa only [abs_mul] using abs_add_le (A - T) (T * (1 - M))
    _ ≤ E + F := by
      rw [abs_sub_comm (1 : ℝ) M]
      exact add_le_add hA ((mul_le_mul hT hm (abs_nonneg _) zero_le_one).trans_eq (one_mul F))
    _ ≤ 2 * (E + F) * M := by nlinarith

theorem shiftedSmoothProductMass_pos_of_mesh {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2) :
    0 < shiftedSmoothProductMass a S :=
  (div_pos (Finset.prod_pos (fun i _ => hS i)) (by norm_num)).trans_le
    (shiftedSmoothProductMass_lower a S hS hδ hδ1 hmesh hsmall)

theorem smoothProductProfile_test_lipschitz {I : Type*} [Fintype I]
    (φ : (I → ℝ) → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    LipschitzWith (L + Fintype.card I * probabilityProfileLipschitz)
      (fun x => smoothProductProfile I x * φ x) := by
  simpa only [one_mul] using lipschitz_real_mul_of_bounds
    (smoothProductProfile I) φ (Bf := 1) (Bg := 1)
    (smoothProductProfile_lipschitz I) hLip
    (fun x => smoothProductProfile_norm_le I x) hφ

theorem smoothProductProfile_real_test_integral_norm_le {I : Type*} [Fintype I]
    (φ : (I → ℝ) → ℝ) (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    ‖∫ x, smoothProductProfile I x * φ x‖ ≤ 1 := by
  have hi : Integrable (smoothProductProfile I) :=
    (smoothProductProfile_contDiff I).continuous.integrable_of_hasCompactSupport
      (smoothProductProfile_compact I)
  rw [← smoothProductProfile_integral I]
  apply norm_integral_le_of_norm_le hi
  filter_upwards [] with x
  rw [norm_mul, Real.norm_of_nonneg (smoothProductProfile_range I x).1]
  exact mul_le_of_le_one_right (smoothProductProfile_range I x).1 (hφ x)

theorem shiftedSmoothProductPMF_test_quadrature {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (φ : (I → ℝ) → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    |(∑' k, (shiftedSmoothProductPMF a S hS hZ k).toReal *
        φ (rectangularLatticePoint a S k)) -
      ∫ x, smoothProductProfile I x * φ x| ≤
      2 * (4 : ℝ) ^ Fintype.card I *
        ((L : ℝ) + 2 * ((Fintype.card I : ℝ) * probabilityProfileLipschitz)) * δ := by
  let f := fun x => smoothProductProfile I x * φ x
  have hsupp (x : I → ℝ) (hx : 1 < ‖x‖) : f x = 0 := by
    simp only [f, smoothProductProfile_zero_outside I x hx, zero_mul]
  have he := rectangularLattice_quadrature f
    (smoothProductProfile_test_lipschitz φ hLip hφ) a S hS
    zero_le_one hδ hδ1 hmesh hsupp
  have hm := rectangularLattice_quadrature (smoothProductProfile I)
    (smoothProductProfile_lipschitz I) a S hS
    zero_le_one hδ hδ1 hmesh (smoothProductProfile_zero_outside I)
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast,
    show 2 * (1 : ℝ) + 2 = 4 by norm_num] at he hm
  rw [smoothProductProfile_integral I] at hm
  change |shiftedSmoothProductMass a S / (∏ i, S i) - 1| ≤ _ at hm
  have hp : 0 < ∏ i, S i := Finset.prod_pos (fun i _ => hS i)
  have hlo : 1 / 2 ≤ shiftedSmoothProductMass a S / (∏ i, S i) := by
    apply (le_div_iff₀ hp).mpr
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      shiftedSmoothProductMass_lower a S hS hδ hδ1 hmesh hsmall
  have hn := normalizedRealQuadrature_error hlo he hm
    (smoothProductProfile_real_test_integral_norm_le φ hφ)
  have heq : (∑' k, (shiftedSmoothProductPMF a S hS hZ k).toReal *
      φ (rectangularLatticePoint a S k)) =
      ((∑' k, f (rectangularLatticePoint a S k)) / (∏ i, S i)) /
        (shiftedSmoothProductMass a S / (∏ i, S i)) := by
    simp only [shiftedSmoothProductPMF_toReal, rectangularWeight, div_mul_eq_mul_div,
      ← tsum_div_const]
    dsimp only [f]
    field_simp
  rw [heq]
  exact hn.trans_eq (by ring)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {I : Type*} [Fintype I]

theorem smoothProductProfile_complex_test_integrable
    (φ : (I → ℝ) → ℂ) (hφ : Continuous φ) :
    Integrable (fun x => (smoothProductProfile I x : ℂ) * φ x) := by
  apply ((Complex.continuous_ofReal.comp
    (smoothProductProfile_contDiff I).continuous).mul hφ).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : I → ℝ) 1)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! hn
  apply hx
  change (smoothProductProfile I x : ℂ) * φ x = 0
  simp only [smoothProductProfile_zero_outside I x hn, Complex.ofReal_zero, zero_mul]

theorem shiftedSmoothProductPMF_complex_test_quadrature
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (φ : (I → ℝ) → ℂ) {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    ‖(∑' k, ((shiftedSmoothProductPMF a S hS hZ k).toReal : ℂ) *
        φ (rectangularLatticePoint a S k)) -
      ∫ x, (smoothProductProfile I x : ℂ) * φ x‖ ≤
      4 * (4 : ℝ) ^ Fintype.card I *
        ((L : ℝ) + 2 * ((Fintype.card I : ℝ) * probabilityProfileLipschitz)) * δ := by
  have hreLip : LipschitzWith L (fun x => (φ x).re) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans
      (by simpa only [dist_eq_norm] using hLip.dist_le_mul x y)
  have himLip : LipschitzWith L (fun x => (φ x).im) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans
      (by simpa only [dist_eq_norm] using hLip.dist_le_mul x y)
  have hre := shiftedSmoothProductPMF_test_quadrature a S hS hZ hδ hδ1 hmesh hsmall
    (fun x => (φ x).re) hreLip
    (fun x => by simpa only [Real.norm_eq_abs] using
      (Complex.abs_re_le_norm (φ x)).trans (hφ x))
  have him := shiftedSmoothProductPMF_test_quadrature a S hS hZ hδ hδ1 hmesh hsmall
    (fun x => (φ x).im) himLip
    (fun x => by simpa only [Real.norm_eq_abs] using
      (Complex.abs_im_le_norm (φ x)).trans (hφ x))
  have hs : Summable (fun k => ((shiftedSmoothProductPMF a S hS hZ k).toReal : ℂ) *
      φ (rectangularLatticePoint a S k)) :=
    finite_weighted_test_summable _ (rectangularWeightIndices a S 1)
      (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ) _
  have hi := smoothProductProfile_complex_test_integrable φ hLip.continuous
  have hire : (∫ x, (smoothProductProfile I x : ℂ) * φ x).re =
      ∫ x, smoothProductProfile I x * (φ x).re := by
    simpa only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using (integral_re hi).symm
  have hiim : (∫ x, (smoothProductProfile I x : ℂ) * φ x).im =
      ∫ x, smoothProductProfile I x * (φ x).im := by
    simpa only [RCLike.im_eq_complex_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using (integral_im hi).symm
  let C := 2 * (4 : ℝ) ^ Fintype.card I *
    ((L : ℝ) + 2 * ((Fintype.card I : ℝ) * probabilityProfileLipschitz)) * δ
  calc
    _ ≤ |((∑' k, ((shiftedSmoothProductPMF a S hS hZ k).toReal : ℂ) *
          φ (rectangularLatticePoint a S k)) -
        ∫ x, (smoothProductProfile I x : ℂ) * φ x).re| +
        |((∑' k, ((shiftedSmoothProductPMF a S hS hZ k).toReal : ℂ) *
          φ (rectangularLatticePoint a S k)) -
        ∫ x, (smoothProductProfile I x : ℂ) * φ x).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ C + C := by
      apply add_le_add
      · simpa only [Complex.sub_re, Complex.re_tsum hs, hire, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hre
      · simpa only [Complex.sub_im, Complex.im_tsum hs, hiim, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using him
    _ = _ := by dsimp only [C]; ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal Classical

variable {K X : Type*} [Fintype K] [Fintype X]

theorem selectedResidueSmoothPMF_singleton_complex_quadrature
    (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (r : ColumnResiduePattern K X modulus) (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus {r} V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ z, (modulus z.2 : ℝ) / V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (K × X) *
      ((Fintype.card (K × X) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (φ : (K × X → ℝ) → ℂ) {A : ℝ≥0} (hLip : LipschitzWith A φ)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    ‖(∑' z, ((selectedResidueSmoothPMF modulus {r} V hV hZ z).toReal : ℂ) *
        φ (fun k => (z k : ℝ) / V k)) -
      ∫ x, (smoothProductProfile (K × X) x : ℂ) * φ x‖ ≤
      4 * (4 : ℝ) ^ Fintype.card (K × X) *
        ((A : ℝ) + 2 * ((Fintype.card (K × X) : ℝ) * probabilityProfileLipschitz)) * δ := by
  rw [selectedResidueSmoothPMF_singleton_normalized_expectation modulus hmodulus r V hV hZ]
  apply shiftedSmoothProductPMF_complex_test_quadrature _ _
    (residueProfileWidth_pos modulus V hmodulus hV)
    (selectedResidueSmooth_singleton_indexMass_pos modulus hmodulus r V hV hZ)
    hδ hδ1 _ hsmall φ hLip hφ
  intro z
  simpa only [residueProfileWidth, one_div_div] using hmesh z

end Erdos3

end

end OAI
