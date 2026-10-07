import Mathlib.Analysis.Calculus.MeanValue
import OAI.Combinatorics.Progressions.Lattices.IntegerImageProbabilityLaw

namespace OAI


namespace Erdos3

open scoped Matrix NNReal

theorem integerFiber_polynomial_error {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (v : I → ℤ) (hv : v ∈ pivotFullImage A B)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R G U V C L ρ : ℝ} (h : ℕ) (hR : 0 ≤ R) (hρ : 0 < ρ)
    (hscale : ∀ j, ρ ≤ T j) (hsmall : (A.det.natAbs : ℝ) ≤ ρ)
    (hcoeff : ∀ i j, |(A i j : ℝ)| ≤ C * L ^ h)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns B T P)‖ ≤ V) :
    |scaledIntegerFiberOutputMass A B S P T f v -
        ((pivotFullImage A B).toAddSubgroup.index : ℝ) *
          normalizedFiberDensity A hA B S P T hS hP f (fun i => (v i : ℝ) / P i)| ≤
      (integerFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R K *
        ((Fintype.card I).factorial * C ^ Fintype.card I)) * L ^ (h * Fintype.card I) / ρ := by
  have hm : (0 : ℤ) < A.det.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hA
  have hδ : 0 ≤ (A.det.natAbs : ℝ) / ρ := div_nonneg (Nat.cast_nonneg _) hρ.le
  have hδ1 : (A.det.natAbs : ℝ) / ρ ≤ 1 := (div_le_one hρ).mpr hsmall
  have hmesh (j : J) : ((A.det.natAbs : ℤ) : ℝ) / T j ≤ (A.det.natAbs : ℝ) / ρ := by
    exact div_le_div_of_nonneg_left (by positivity) hρ (hscale j)
  have ht := integerFiber_uniform_quadrature A hA B v hv hm Int.dvd_natAbs_self
    S P T hS hP hT f hf hR hδ hδ1 hmesh hsupport hindex hinv hcol
  have hconst : 0 ≤ integerFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R K :=
    integerFiberErrorConstant_nonneg _ _ K ((Nat.cast_nonneg _).trans hindex)
      ((norm_nonneg _).trans hinv) hR
  have hdet := integerPivot_polynomial_period_bound A h hcoeff
  calc
    _ ≤ _ := ht
    _ ≤ integerFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R K *
        ((((Fintype.card I).factorial * C ^ Fintype.card I) * L ^ (h * Fintype.card I)) / ρ) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hdet hρ.le) hconst
    _ = _ := by ring

theorem integerFiber_c1_polynomial_error {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (v : I → ℤ) (hv : v ∈ pivotFullImage A B)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) {K : ℝ≥0} (hf : ContDiff ℝ 1 f)
    (hderiv : ∀ p, ‖fderiv ℝ f p‖₊ ≤ K)
    {R G U V C L ρ : ℝ} (h : ℕ) (hR : 0 ≤ R) (hρ : 0 < ρ)
    (hscale : ∀ j, ρ ≤ T j) (hsmall : (A.det.natAbs : ℝ) ≤ ρ)
    (hcoeff : ∀ i j, |(A i j : ℝ)| ≤ C * L ^ h)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns B T P)‖ ≤ V) :
    |scaledIntegerFiberOutputMass A B S P T f v -
        ((pivotFullImage A B).toAddSubgroup.index : ℝ) *
          normalizedFiberDensity A hA B S P T hS hP f (fun i => (v i : ℝ) / P i)| ≤
      (integerFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R K *
        ((Fintype.card I).factorial * C ^ Fintype.card I)) * L ^ (h * Fintype.card I) / ρ :=
  integerFiber_polynomial_error A hA B v hv S P T hS hP hT f
    (lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by norm_num)) hderiv)
    h hR hρ hscale hsmall hcoeff hsupport hindex hinv hcol

end Erdos3


namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

theorem normalizedIntegerFiber_polynomial_error {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (v : I → ℤ) (hv : v ∈ pivotFullImage A B)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R G U V C L ρ H : ℝ} (h : ℕ) (hR : 0 ≤ R) (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hscaleS : ∀ i, ρ ≤ S i) (hscaleT : ∀ j, ρ ≤ T j) (hsmall : (A.det.natAbs : ℝ) ≤ ρ)
    (hcoeff : ∀ i j, |(A i j : ℝ)| ≤ C * L ^ h)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hmass : (∫ p, f p) = 1)
    (hsmallMass : (2 * R + 2) ^ (Fintype.card I + Fintype.card J) * K *
      ((A.det.natAbs : ℝ) / ρ) ≤ 1 / 2)
    (hbound : ∀ p, ‖f p‖ ≤ H)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns B T P)‖ ≤ V) :
    0 < scaledInputMass f S T ∧
      |normalizedIntegerFiberOutputMass A B S P T f v -
        ((pivotFullImage A B).toAddSubgroup.index : ℝ) *
          normalizedFiberDensity A hA B S P T hS hP f (fun i => (v i : ℝ) / P i)| ≤
      (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R H K *
        ((Fintype.card I).factorial * C ^ Fintype.card I)) * L ^ (h * Fintype.card I) / ρ := by
  have hm : (0 : ℤ) < A.det.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hA
  have hq1 : (1 : ℝ) ≤ A.det.natAbs := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hA))
  have hδ : 0 ≤ (A.det.natAbs : ℝ) / ρ := div_nonneg (Nat.cast_nonneg _) hρ.le
  have hδ1 : (A.det.natAbs : ℝ) / ρ ≤ 1 := (div_le_one hρ).mpr hsmall
  have hmeshS (i) : 1 / S i ≤ (A.det.natAbs : ℝ) / ρ :=
    (div_le_div_of_nonneg_left zero_le_one hρ (hscaleS i)).trans
      (div_le_div_of_nonneg_right hq1 hρ.le)
  have hmeshT (j) : ((A.det.natAbs : ℤ) : ℝ) / T j ≤ (A.det.natAbs : ℝ) / ρ :=
    div_le_div_of_nonneg_left (by positivity) hρ (hscaleT j)
  have ht := normalizedIntegerFiber_uniform_error A hA B v hv hm Int.dvd_natAbs_self
    S P T hS hP hT f hf hR hδ hδ1 hH hmeshS hmeshT hsupport hmass hsmallMass hbound hindex hinv hcol
  refine ⟨ht.1, ht.2.trans ?_⟩
  have hG : 0 ≤ G := (Nat.cast_nonneg _).trans hindex
  have hU : 0 ≤ U := (norm_nonneg _).trans hinv
  have hbase := integerFiberErrorConstant_nonneg (Fintype.card I) (Fintype.card J) (V := V) K hG hU hR
  have hconst : 0 ≤ normalizedFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R H K := by
    unfold normalizedFiberErrorConstant
    positivity
  have hdet := integerPivot_polynomial_period_bound A h hcoeff
  calc
    _ ≤ normalizedFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R H K *
        ((((Fintype.card I).factorial * C ^ Fintype.card I) * L ^ (h * Fintype.card I)) / ρ) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hdet hρ.le) hconst
    _ = _ := by ring

theorem normalizedIntegerFiber_c1_probability_error {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (v : I → ℤ) (hv : v ∈ pivotFullImage A B)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p) {K : ℝ≥0} (hf : ContDiff ℝ 1 f)
    (hderiv : ∀ p, ‖fderiv ℝ f p‖₊ ≤ K)
    {R G U V C L ρ H : ℝ} (h : ℕ) (hR : 0 ≤ R) (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hscaleS : ∀ i, ρ ≤ S i) (hscaleT : ∀ j, ρ ≤ T j) (hsmall : (A.det.natAbs : ℝ) ≤ ρ)
    (hcoeff : ∀ i j, |(A i j : ℝ)| ≤ C * L ^ h)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hmass : (∫ p, f p) = 1)
    (hsmallMass : (2 * R + 2) ^ (Fintype.card I + Fintype.card J) * K *
      ((A.det.natAbs : ℝ) / ρ) ≤ 1 / 2)
    (hbound : ∀ p, ‖f p‖ ≤ H)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns B T P)‖ ≤ V) :
    ∃ hM : 0 < scaledInputMass f S T,
      |(∏ i, P i) * (integerImagePMF A B f hf0 S T hS hT hsupport hM v).toReal -
        ((pivotFullImage A B).toAddSubgroup.index : ℝ) *
          normalizedFiberDensity A hA B S P T hS hP f (fun i => (v i : ℝ) / P i)| ≤
      (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R H K *
        ((Fintype.card I).factorial * C ^ Fintype.card I)) * L ^ (h * Fintype.card I) / ρ := by
  have ht := normalizedIntegerFiber_polynomial_error A hA B v hv S P T hS hP hT f
    (lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by norm_num)) hderiv)
    h hR hρ hH hscaleS hscaleT hsmall hcoeff hsupport hmass hsmallMass hbound hindex hinv hcol
  refine ⟨ht.1, ?_⟩
  rw [← normalizedIntegerFiberOutputMass_pmf A B f hf0 S P T hS hT hsupport ht.1 v]
  exact ht.2

end Erdos3

end OAI
