import OAI.Combinatorics.Progressions.Estimates.CoefficientRowReindex
import OAI.Combinatorics.Progressions.Probability.FiniteCountDensityError

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem mem_rectangularWeightIndices_zero_of_norm_le {I : Type*} [Fintype I]
    (P : I → ℝ) (hP : ∀ i, 0 < P i) {T : ℝ} (v : I → ℤ)
    (hv : ‖fun i => (v i : ℝ) / P i‖ ≤ T) :
    v ∈ rectangularWeightIndices (fun _ => 0) P T := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi : |(v i : ℝ) / P i| ≤ T :=
    (norm_le_pi_norm (fun j => (v j : ℝ) / P j) i).trans hv
  obtain ⟨hlo, hhi⟩ := abs_le.mp hi
  apply Finset.mem_Icc.mpr
  exact ⟨Int.ceil_le.mpr (by nlinarith [(le_div_iff₀ (hP i)).mp hlo]),
    Int.le_floor.mpr (by nlinarith [(div_le_iff₀ (hP i)).mp hhi])⟩

theorem coefficientImagePMF_zero_off_box {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (S : J → ℝ) (P : I → ℝ)
    (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) {R T : ℝ}
    (hs : ∀ x, R < ‖x‖ → f x = 0) (hZ : 0 < coefficientWeightSum f S)
    (hbox : ‖matrixSupCLM (normalizedIntegerColumns A S P)‖ * R ≤ T)
    (v : I → ℤ) (hv : v ∉ rectangularWeightIndices (fun _ => 0) P T) :
    coefficientImagePMF A f hf0 S hS hs hZ v = 0 := by
  apply (PMF.apply_eq_zero_iff _ v).mpr
  intro hm
  obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
  have hzn : ‖fun j => (z j : ℝ) / S j‖ ≤ R := by
    by_contra! hn
    have hzero := hs _ hn
    have hpos := ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hz)
      (PMF.apply_ne_top _ _)
    rw [coefficientPMF_apply] at hpos
    change 0 < f (fun j => (z j : ℝ) / S j) / coefficientWeightSum f S at hpos
    rw [hzero, zero_div] at hpos
    exact (lt_irrefl 0) hpos
  apply hv
  apply mem_rectangularWeightIndices_zero_of_norm_le P hP
  rw [← normalizedIntegerColumns_mulVec A S P (fun j => (hS j).ne') z,
    ← matrixSupCLM_apply]
  exact ((matrixSupCLM (normalizedIntegerColumns A S P)).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left hzn (norm_nonneg _)).trans hbox)

theorem coefficientImageMask_zero_off_box {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) {R T : ℝ} (hs : ∀ x, R < ‖x‖ → f x = 0)
    (hbox : (‖matrixSupCLM (normalizedIntegerPivot (A.submatrix id s)
        (fun i => S (s i)) P)‖ +
      ‖matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s)
        (fun j => S j.val) P)‖) * R ≤ T)
    (v : I → ℤ) (hv : v ∉ rectangularWeightIndices (fun _ => 0) P T) :
    coefficientImageMask A P (selectedCoefficientDensity A s hA S P hS hP f) v = 0 := by
  classical
  have hn : T < ‖fun i => (v i : ℝ) / P i‖ := lt_of_not_ge (fun hn =>
    hv (mem_rectangularWeightIndices_zero_of_norm_le P hP v hn))
  have hd : selectedCoefficientDensity A s hA S P hS hP f
      (fun i => (v i : ℝ) / P i) = 0 := by
    apply pivotOutputDensity_zero_outside _ _ (selectedCoefficientProfile_zero_outside s hs)
    rw [normalizedPivotEquiv_coe]
    exact hbox.trans_lt hn
  simp only [coefficientImageMask, hd, mul_zero, ite_self]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def coefficientGridProxy (A : Matrix I J ℤ) (s : I ↪ J)
    (hA : (A.submatrix id s).det ≠ 0) (S : J → ℝ) (P : I → ℝ)
    (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i) (f : (J → ℝ) → ℝ) (v : I → ℤ) : ℝ :=
  coefficientImageMask A P (selectedCoefficientDensity A s hA S P hS hP f) v / ∏ i, P i

theorem coefficientGridProxy_nonneg (A : Matrix I J ℤ) (s : I ↪ J)
    (hA : (A.submatrix id s).det ≠ 0) (S : J → ℝ) (P : I → ℝ)
    (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (v : I → ℤ) :
    0 ≤ coefficientGridProxy A s hA S P hS hP f v := by
  apply div_nonneg _ (Finset.prod_nonneg (fun i _ => (hP i).le))
  unfold coefficientImageMask
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (pivotOutputDensity_nonneg _ _
      (selectedCoefficientProfile_nonneg s hf0) _)
  · exact le_rfl

theorem coefficientGridProxy_integrable (A : Matrix I J ℤ) (s : I ↪ J)
    (hA : (A.submatrix id s).det ≠ 0) (S : J → ℝ) (P : I → ℝ)
    (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) {R T : ℝ} (hs : ∀ x, R < ‖x‖ → f x = 0)
    (hbox : (‖matrixSupCLM (normalizedIntegerPivot (A.submatrix id s)
        (fun i => S (s i)) P)‖ +
      ‖matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s)
        (fun j => S j.val) P)‖) * R ≤ T) :
    Integrable (coefficientGridProxy A s hA S P hS hP f) Measure.count := by
  apply count_integrable_of_zero_off_finset (rectangularWeightIndices (fun _ => 0) P T)
  intro v hv
  rw [coefficientGridProxy, coefficientImageMask_zero_off_box A s hA S P hS hP f hs hbox v hv,
    zero_div]

theorem coefficientImage_count_error (A : Matrix I J ℤ) (s : I ↪ J)
    (hA : (A.submatrix id s).det ≠ 0) (S : J → ℝ) (P : I → ℝ)
    (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i) (hP1 : ∀ i, 1 ≤ P i)
    (f : (J → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) {R T E : ℝ}
    (hs : ∀ x, R < ‖x‖ → f x = 0) (hZ : 0 < coefficientWeightSum f S)
    (hT : 0 ≤ T)
    (hdiscrete : ‖matrixSupCLM (normalizedIntegerColumns A S P)‖ * R ≤ T)
    (hcontinuous : (‖matrixSupCLM (normalizedIntegerPivot (A.submatrix id s)
        (fun i => S (s i)) P)‖ +
      ‖matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s)
        (fun j => S j.val) P)‖) * R ≤ T)
    (he : ∀ v, |(∏ i, P i) * (coefficientImagePMF A f hf0 S hS hs hZ v).toReal -
      coefficientImageMask A P (selectedCoefficientDensity A s hA S P hS hP f) v| ≤ E) :
    (∫ v, |(coefficientImagePMF A f hf0 S hS hs hZ v).toReal -
      coefficientGridProxy A s hA S P hS hP f v| ∂Measure.count) ≤
      (2 * T + 1) ^ Fintype.card I * E := by
  apply rectangular_count_density_l1 (fun _ => 0) P hP1 hT
    ((abs_nonneg _).trans (he 0))
  · intro v hv
    rw [coefficientImagePMF_zero_off_box A S P hS hP f hf0 hs hZ hdiscrete v hv,
      ENNReal.toReal_zero]
  · exact coefficientImageMask_zero_off_box A s hA S P hS hP f hs hcontinuous
  · exact he

theorem coefficientImage_polynomial_l1 (A : Matrix I J ℤ) (s : I ↪ J)
    (hA : (A.submatrix id s).det ≠ 0) (S : J → ℝ) (P : I → ℝ)
    (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i) (hP1 : ∀ i, 1 ≤ P i)
    (f : (J → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R T G U V C L ρ H : ℝ} (h : ℕ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hscale : ∀ j, ρ ≤ S j) (hsmall : ((A.submatrix id s).det.natAbs : ℝ) ≤ ρ)
    (hcoeff : ∀ i j, |(A i (s j) : ℝ)| ≤ C * L ^ h)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hmass : (∫ x, f x) = 1)
    (hsmallMass : (2 * R + 2) ^ (Fintype.card I + Fintype.card (UnselectedColumn s)) * K *
      (((A.submatrix id s).det.natAbs : ℝ) / ρ) ≤ 1 / 2)
    (hbound : ∀ x, ‖f x‖ ≤ H) (hindex : (A.mulVecLin.range.toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(matrixSupCLM (normalizedIntegerPivot (A.submatrix id s)
      (fun i => S (s i)) P)).inverse‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s)
      (fun j => S j.val) P)‖ ≤ V)
    (hdiscrete : ‖matrixSupCLM (normalizedIntegerColumns A S P)‖ * R ≤ T)
    (hcontinuous : (‖matrixSupCLM (normalizedIntegerPivot (A.submatrix id s)
        (fun i => S (s i)) P)‖ +
      ‖matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s)
        (fun j => S j.val) P)‖) * R ≤ T) :
    ∃ hZ : 0 < coefficientWeightSum f S,
      (∫ v, |(coefficientImagePMF A f hf0 S hS hsupport hZ v).toReal -
        coefficientGridProxy A s hA S P hS hP f v| ∂Measure.count) ≤
        (2 * T + 1) ^ Fintype.card I *
          ((normalizedFiberErrorConstant (Fintype.card I) (Fintype.card (UnselectedColumn s))
            G U V R H K * ((Fintype.card I).factorial * C ^ Fintype.card I)) *
            L ^ (h * Fintype.card I) / ρ) := by
  obtain ⟨hZ, he⟩ := coefficientImage_polynomial_error A s hA S P hS hP f hf0 hf
    h hR hρ hH hscale hsmall hcoeff hsupport hmass hsmallMass hbound hindex hinv hcol
  exact ⟨hZ, coefficientImage_count_error A s hA S P hS hP hP1 f hf0 hsupport hZ
    hT hdiscrete hcontinuous he⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem normalized_selected_split_norm_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (P : I → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (he : ∀ i j, |normalizedIntegerColumns A S P i j| ≤ C) :
    ‖matrixSupCLM (normalizedIntegerPivot (A.submatrix id s) (fun i => S (s i)) P)‖ +
      ‖matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s)
        (fun j => S j.val) P)‖ ≤ Fintype.card J * C := by
  have hp : ‖matrixSupCLM (normalizedIntegerPivot (A.submatrix id s)
      (fun i => S (s i)) P)‖ ≤ Fintype.card I * C := by
    rw [← normalizedIntegerColumns_submatrix]
    exact matrixSupCLM_norm_le _ hC (fun i j => he i (s j))
  have hc : (Fintype.card I : ℝ) + Fintype.card (UnselectedColumn s) = Fintype.card J := by
    exact_mod_cast (show Fintype.card I + Fintype.card (UnselectedColumn s) = Fintype.card J from
      by simpa only [Fintype.card_sum] using Fintype.card_congr (selectedColumnEquiv s))
  calc
    _ ≤ Fintype.card I * C + Fintype.card (UnselectedColumn s) * C :=
      add_le_add hp (normalized_remainingMatrixColumns_norm A s S P hC he)
    _ = _ := by rw [← add_mul, hc]

def coefficientGridBoxFactor (i j : ℕ) (C R : ℝ) : ℝ :=
  (2 * (j * C * R) + 1) ^ i

theorem coefficientGridBoxFactor_pos (i j : ℕ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 < coefficientGridBoxFactor i j C R := by
  unfold coefficientGridBoxFactor
  positivity

theorem coefficientImage_l1_of_control {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {H L C U G : ℝ} (h : ℕ) (ctrl : CoefficientFiberControl A s S H L h C U G)
    (hH : 0 < H) (hH1 : 1 ≤ H) (hC : 0 ≤ C)
    (f : (J → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) {R E : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x, R < ‖x‖ → f x = 0) (hZ : 0 < coefficientWeightSum f S)
    (he : ∀ v, |H ^ Fintype.card I * (coefficientImagePMF A f hf0 S hS hs hZ v).toReal -
      coefficientImageMask A (fun _ => H)
        (selectedCoefficientDensity A s ctrl.det_ne_zero S (fun _ => H) hS (fun _ => hH) f) v| ≤ E) :
    (∫ v, |(coefficientImagePMF A f hf0 S hS hs hZ v).toReal -
      coefficientGridProxy A s ctrl.det_ne_zero S (fun _ => H) hS (fun _ => hH) f v|
        ∂Measure.count) ≤ coefficientGridBoxFactor (Fintype.card I) (Fintype.card J) C R * E := by
  apply coefficientImage_count_error A s ctrl.det_ne_zero S (fun _ => H) hS
    (fun _ => hH) (fun _ => hH1) f hf0 hs hZ (by positivity)
  · exact mul_le_mul_of_nonneg_right
      (matrixSupCLM_norm_le _ hC ctrl.normalized_entry_bound) hR
  · exact mul_le_mul_of_nonneg_right
      (normalized_selected_split_norm_le A s S (fun _ => H) hC ctrl.normalized_entry_bound) hR
  · simpa only [Finset.prod_const, Finset.card_univ] using he

theorem coefficientGridProxy_integrable_of_control {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {H L C U G : ℝ} (h : ℕ) (ctrl : CoefficientFiberControl A s S H L h C U G)
    (hH : 0 < H) (hC : 0 ≤ C) (f : (J → ℝ) → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x, R < ‖x‖ → f x = 0) :
    Integrable (coefficientGridProxy A s ctrl.det_ne_zero S (fun _ => H) hS (fun _ => hH) f)
      Measure.count :=
  coefficientGridProxy_integrable A s ctrl.det_ne_zero S (fun _ => H) hS (fun _ => hH) f hs
    (mul_le_mul_of_nonneg_right
      (normalized_selected_split_norm_le A s S (fun _ => H) hC ctrl.normalized_entry_bound) hR)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem coefficientImage_enormous_l1_of_control {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {H L C U G : ℝ} (h : ℕ) (ctrl : CoefficientFiberControl A s S H L h C U G)
    (hL : 0 < L) (hH : 0 < H) (hH1 : 1 ≤ H) (hC : 0 ≤ C)
    (f : (J → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R Hcap : ℝ} (hR : 0 ≤ R) (hcap : 0 ≤ Hcap)
    (hs : ∀ x, R < ‖x‖ → f x = 0) (hmass : (∫ x, f x) = 1)
    (hbound : ∀ x, ‖f x‖ ≤ Hcap)
    (hlarge : 2 * (1 + (2 * R + 2) ^ (Fintype.card I + Fintype.card (UnselectedColumn s)) * K) *
      ((Fintype.card I).factorial * C ^ Fintype.card I) * L ^ (h * (Fintype.card I + 1)) ≤ H) :
    ∃ hZ : 0 < coefficientWeightSum f S,
      (∫ v, |(coefficientImagePMF A f hf0 S hS hs hZ v).toReal -
        coefficientGridProxy A s ctrl.det_ne_zero S (fun _ => H) hS (fun _ => hH) f v|
          ∂Measure.count) ≤
        (coefficientGridBoxFactor (Fintype.card I) (Fintype.card J) C R *
          (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card (UnselectedColumn s))
            G U (Fintype.card (UnselectedColumn s) * C) R Hcap K *
            ((Fintype.card I).factorial * C ^ Fintype.card I))) *
          L ^ (h * (Fintype.card I + 1)) / H := by
  obtain ⟨hZ, he⟩ := coefficientImage_enormous_of_control A s S hS h ctrl hL hH hC
    f hf0 hf hR hcap hs hmass hbound hlarge
  refine ⟨hZ, (coefficientImage_l1_of_control A s S hS h ctrl hH hH1 hC f hf0 hR hs hZ he).trans_eq ?_⟩
  ring

end Erdos3

end

end OAI
