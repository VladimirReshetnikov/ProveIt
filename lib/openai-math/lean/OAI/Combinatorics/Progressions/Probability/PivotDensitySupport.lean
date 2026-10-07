import OAI.Combinatorics.Progressions.Estimates.PivotOutputLipschitz
import OAI.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation

namespace OAI


namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

theorem splitPivotDensity_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (v : I → ℝ) :
    pivotOutputDensity A (splitFreeColumns B C) (splitFreeProfile f g) v =
      ∫ n, g n * pivotOutputDensity A B f (v - C n) := by
  let F : (J → ℝ) × (N → ℝ) → ℝ := fun p =>
    f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2
  have hi : Integrable F := splitFreeProfile_slice_integrable A B C hf hg hfs hgs v
  rw [pivotOutputDensity_formula]
  change inverseJacobian A * (∫ y, splitInputProfile F y) = _
  rw [splitInputProfile_integral, Measure.volume_eq_prod, integral_prod_symm _ hi,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with n
  have heq (y : J → ℝ) : v - (B y + C n) = (v - C n) - B y := by abel
  simp only [F, heq, integral_mul_const, pivotOutputDensity_formula]
  ring

theorem splitPivotDensity_displacement (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : Continuous g) {R S δ : ℝ} (hR : 0 ≤ R)
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1)
    (hmove : ∀ n, g n ≠ 0 → ‖C n‖ ≤ δ) (v : I → ℝ) :
    |pivotOutputDensity A (splitFreeColumns B C) (splitFreeProfile f g) v -
      pivotOutputDensity A B f v| ≤
        (inverseJacobian A * (2 * R) ^ Fintype.card J * K *
          ‖A.symm.toContinuousLinearMap‖) * δ := by
  let L := inverseJacobian A * (2 * R) ^ Fintype.card J * K * ‖A.symm.toContinuousLinearMap‖
  have hL : 0 ≤ L := by
    have hJ := inverseJacobian_pos A
    dsimp [L]
    positivity
  have hd : Continuous (pivotOutputDensity A B f) := by
    have hl : LipschitzWith (Real.toNNReal L) (pivotOutputDensity A B f) := by
      apply LipschitzWith.of_dist_le'
      intro u w
      simpa only [dist_eq_norm, Real.norm_eq_abs, L] using
        pivotOutputDensity_output_bound A B hf hR hfs u w
    exact hl.continuous
  have hi := compactBox_integrable
    (fun n => g n * pivotOutputDensity A B f (v - C n))
    (by fun_prop) S (fun n hn => by rw [hgs n hn, zero_mul])
  have hgi := compactBox_integrable g hg S hgs
  have hc := hgi.mul_const (pivotOutputDensity A B f v)
  have heq : (∫ n, g n * pivotOutputDensity A B f v) = pivotOutputDensity A B f v := by
    rw [integral_mul_const, hgmass, one_mul]
  rw [splitPivotDensity_formula A B C hf.continuous hg hfs hgs v, ← heq, ← integral_sub hi hc]
  have hb : ∀ n, ‖g n * pivotOutputDensity A B f (v - C n) -
      g n * pivotOutputDensity A B f v‖ ≤ g n * (L * δ) := by
    intro n
    by_cases hn : g n = 0
    · simp [hn]
    · rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hg0 n), Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (hg0 n)
      apply (pivotOutputDensity_output_bound A B hf hR hfs (v - C n) v).trans
      have hdif : (v - C n) - v = -(C n) := by abel
      rw [hdif, norm_neg]
      exact mul_le_mul_of_nonneg_left (hmove n hn) hL
  have ht := norm_integral_le_of_norm_le (hgi.mul_const (L * δ)) (Filter.Eventually.of_forall hb)
  rw [integral_mul_const, hgmass, one_mul] at ht
  simpa only [Real.norm_eq_abs] using ht

end Erdos3


namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def spatialKernelErrorConstant (j d : ℕ) (U R : ℝ) (K : ℝ≥0) : ℝ :=
  (j.factorial * U ^ j) * (2 * R) ^ d * K * U

theorem spatialKernelErrorConstant_nonneg (j d : ℕ) {U R : ℝ} (K : ℝ≥0)
    (hU : 0 ≤ U) (hR : 0 ≤ R) : 0 ≤ spatialKernelErrorConstant j d U R K := by
  unfold spatialKernelErrorConstant
  positivity

theorem supported_column_displacement {I N : Type*} [Fintype I] [Fintype N]
    (C : (N → ℝ) →L[ℝ] (I → ℝ)) (g : (N → ℝ) → ℝ) {R δ : ℝ}
    (hgs : ∀ n, R < ‖n‖ → g n = 0) (hC : ‖C‖ * R ≤ δ)
    (n : N → ℝ) (hn : g n ≠ 0) : ‖C n‖ ≤ δ := by
  have hnorm : ‖n‖ ≤ R := by
    by_contra! h
    exact hn (hgs n h)
  exact (C.le_opNorm n).trans ((mul_le_mul_of_nonneg_left hnorm (norm_nonneg C)).trans hC)

theorem normalizedSplitDensity_displacement {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (C : Matrix I N ℤ)
    (S P : I → ℝ) (T : J → ℝ) (Q : N → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : Continuous g) {R Rn δ U : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, Rn < ‖n‖ → g n = 0)
    (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hmove : ∀ n, g n ≠ 0 → ‖matrixSupCLM (normalizedIntegerColumns C Q P) n‖ ≤ δ)
    (v : I → ℝ) :
    |normalizedFiberDensity A hA (Matrix.fromCols B C) S P (Sum.elim T Q) hS hP
        (splitFreeProfile f g) v - normalizedFiberDensity A hA B S P T hS hP f v| ≤
      spatialKernelErrorConstant (Fintype.card I) (Fintype.card J) U R K * δ := by
  unfold normalizedFiberDensity
  rw [normalizedIntegerColumns_split]
  have h := splitPivotDensity_displacement (normalizedPivotEquiv A hA S P hS hP)
    (matrixSupCLM (normalizedIntegerColumns B T P))
    (matrixSupCLM (normalizedIntegerColumns C Q P)) hf hg hR hfs hgs hg0 hgmass hmove v
  have hU : 0 ≤ U := (norm_nonneg _).trans hinv
  have hJ := inverseJacobian_le_norm_bound (normalizedPivotEquiv A hA S P hS hP) hinv
  apply h.trans
  unfold spatialKernelErrorConstant
  gcongr

end Erdos3


namespace Erdos3

open MeasureTheory

theorem pivotOutputDensity_zero_outside {I J : Type*} [Fintype I] [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {R : ℝ}
    (hs : ∀ p, R < ‖p‖ → f p = 0) (v : I → ℝ)
    (hv : (‖A.toContinuousLinearMap‖+‖B‖)*R < ‖v‖) :
    pivotOutputDensity A B f v = 0 := by
  have he (y : J → ℝ) : f (y,A.symm (v-B y)) = 0 := by
    by_contra hn
    have hp : ‖(y,A.symm (v-B y))‖ ≤ R := le_of_not_gt (fun h => hn (hs _ h))
    have hy := (norm_fst_le (y,A.symm (v-B y))).trans hp
    have ha := (norm_snd_le (y,A.symm (v-B y))).trans hp
    have hv' : v = A (A.symm (v-B y)) + B y := by rw [A.apply_symm_apply]; abel
    have hb : ‖v‖ ≤ (‖A.toContinuousLinearMap‖+‖B‖)*R := by
      calc
        ‖v‖ = ‖A (A.symm (v-B y)) + B y‖ := congrArg norm hv'
        _ ≤ ‖A (A.symm (v-B y))‖ + ‖B y‖ := norm_add_le _ _
        _ ≤ ‖A.toContinuousLinearMap‖*‖A.symm (v-B y)‖ + ‖B‖*‖y‖ :=
          add_le_add (A.toContinuousLinearMap.le_opNorm _) (B.le_opNorm _)
        _ ≤ ‖A.toContinuousLinearMap‖*R + ‖B‖*R := by gcongr
        _ = _ := by ring
    exact (not_le_of_gt hv) hb
  rw [pivotOutputDensity_formula]
  simp only [he, integral_zero, mul_zero]

theorem splitPivotDensity_zero_outside {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) {R S T : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (hC : ‖C‖ ≤ T) (v : I → ℝ) (hv : (‖A.toContinuousLinearMap‖+‖B‖)*R+T*S < ‖v‖) :
    pivotOutputDensity A (splitFreeColumns B C) (splitFreeProfile f g) v = 0 := by
  rw [splitPivotDensity_formula A B C hf hg hfs hgs v]
  have he (n : N → ℝ) : g n * pivotOutputDensity A B f (v-C n) = 0 := by
    by_cases hn : g n = 0
    · simp only [hn, zero_mul]
    · have hnS : ‖n‖ ≤ S := le_of_not_gt (fun h => hn (hgs n h))
      have hCn : ‖C n‖ ≤ T*S := (C.le_opNorm n).trans
        (mul_le_mul hC hnS (norm_nonneg _) ((norm_nonneg C).trans hC))
      have hdiff : (‖A.toContinuousLinearMap‖+‖B‖)*R < ‖v-C n‖ := by
        have ht : ‖v‖ ≤ ‖v-C n‖+‖C n‖ := by
          simpa only [sub_add_cancel] using norm_add_le (v-C n) (C n)
        linarith
      rw [pivotOutputDensity_zero_outside A B hfs _ hdiff, mul_zero]
  simp only [he, integral_zero]

end Erdos3

end OAI
