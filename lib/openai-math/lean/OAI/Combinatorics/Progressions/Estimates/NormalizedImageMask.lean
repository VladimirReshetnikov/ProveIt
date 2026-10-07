import OAI.Combinatorics.Progressions.Polynomial.NormalizedFiberPolynomialBound

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

noncomputable def maskedIntegerImageDensity {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (P : I → ℝ) (f : (I → ℝ) → ℝ)
    (v : I → ℤ) : ℝ := by
  classical
  exact if v ∈ pivotFullImage A B then
    ((pivotFullImage A B).toAddSubgroup.index : ℝ) * f (fun i => (v i : ℝ) / P i) else 0

theorem maskedIntegerImageDensity_error {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (P : I → ℝ) (f g : (I → ℝ) → ℝ)
    {G ε : ℝ} (hε : 0 ≤ ε)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hfg : ∀ x, |f x - g x| ≤ ε) (v : I → ℤ) :
    |maskedIntegerImageDensity A B P f v - maskedIntegerImageDensity A B P g v| ≤ G * ε := by
  classical
  by_cases hv : v ∈ pivotFullImage A B
  · simp only [maskedIntegerImageDensity, hv, ite_true, ← mul_sub, abs_mul]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ (pivotFullImage A B).toAddSubgroup.index from Nat.cast_nonneg _)]
    exact mul_le_mul hindex (hfg _) (abs_nonneg _) ((Nat.cast_nonneg _).trans hindex)
  · simp only [maskedIntegerImageDensity, hv, ite_false, sub_self, abs_zero]
    exact mul_nonneg ((Nat.cast_nonneg _).trans hindex) hε

theorem normalizedIntegerImage_polynomial_error {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p) {K : ℝ≥0} (hf : LipschitzWith K f)
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
    ∃ hM : 0 < scaledInputMass f S T, ∀ v,
      |(∏ i, P i) * (integerImagePMF A B f hf0 S T hS hT hsupport hM v).toReal -
        maskedIntegerImageDensity A B P (normalizedFiberDensity A hA B S P T hS hP f) v| ≤
      (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R H K *
        ((Fintype.card I).factorial * C ^ Fintype.card I)) * L ^ (h * Fintype.card I) / ρ := by
  classical
  have ht0 := normalizedIntegerFiber_polynomial_error A hA B 0 (Submodule.zero_mem _)
    S P T hS hP hT f hf h hR hρ hH hscaleS hscaleT hsmall hcoeff hsupport hmass
    hsmallMass hbound hindex hinv hcol
  refine ⟨ht0.1, fun v => ?_⟩
  rw [← normalizedIntegerFiberOutputMass_pmf A B f hf0 S P T hS hT hsupport ht0.1 v]
  by_cases hv : v ∈ pivotFullImage A B
  · simp only [maskedIntegerImageDensity, hv, ite_true]
    exact (normalizedIntegerFiber_polynomial_error A hA B v hv
      S P T hS hP hT f hf h hR hρ hH hscaleS hscaleT hsmall hcoeff hsupport hmass
      hsmallMass hbound hindex hinv hcol).2
  · rw [normalizedIntegerFiberOutputMass_zero_off_image A B S P T f v hv]
    simp only [maskedIntegerImageDensity, hv, ite_false, sub_self, abs_zero]
    exact (abs_nonneg _).trans ht0.2

end Erdos3

end

end OAI
