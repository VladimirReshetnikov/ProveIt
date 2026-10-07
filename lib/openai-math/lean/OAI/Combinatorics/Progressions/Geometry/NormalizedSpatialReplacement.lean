import OAI.Combinatorics.Progressions.Estimates.NormalizedImageMask
import OAI.Combinatorics.Progressions.Estimates.PeelingDecomposition
import OAI.Combinatorics.Progressions.Probability.NormalizedJetDensitySupport

namespace OAI


namespace Erdos3

open scoped BigOperators

theorem norm_weighted_density_mean_sub_le {X : Type*} (s : Finset X)
    (D a b : X → ℝ) (φ : X → ℂ) {ε : ℝ}
    (hD : ∀ x ∈ s, 0 ≤ D x) (hφ : ∀ x ∈ s, ‖φ x‖ ≤ 1)
    (hab : ∀ x ∈ s, |a x - b x| ≤ ε) :
    ‖(𝔼 x ∈ s, ((D x * a x : ℝ) : ℂ) * φ x) -
      (𝔼 x ∈ s, ((D x * b x : ℝ) : ℂ) * φ x)‖ ≤ ε * (𝔼 x ∈ s, D x) := by
  rw [← Finset.expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  calc
    _ ≤ 𝔼 x ∈ s, ε * D x := by
      apply Finset.expect_le_expect
      intro x hx
      have heq : ((D x * a x : ℝ) : ℂ) * φ x - ((D x * b x : ℝ) : ℂ) * φ x =
          ((D x * (a x - b x) : ℝ) : ℂ) * φ x := by push_cast; ring
      rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hD x hx)]
      calc
        _ ≤ D x * |a x - b x| * 1 :=
          mul_le_mul_of_nonneg_left (hφ x hx) (mul_nonneg (hD x hx) (abs_nonneg _))
        _ ≤ ε * D x := by
          rw [mul_one, mul_comm ε]
          exact mul_le_mul_of_nonneg_left (hab x hx) (hD x hx)
    _ = _ := (Finset.mul_expect s D ε).symm

theorem norm_weighted_density_mean_sub_le_of_mass {X : Type*} (s : Finset X)
    (D a b : X → ℝ) (φ : X → ℂ) {ε M : ℝ} (hε : 0 ≤ ε)
    (hD : ∀ x ∈ s, 0 ≤ D x) (hφ : ∀ x ∈ s, ‖φ x‖ ≤ 1)
    (hab : ∀ x ∈ s, |a x - b x| ≤ ε) (hM : (𝔼 x ∈ s, D x) ≤ M) :
    ‖(𝔼 x ∈ s, ((D x * a x : ℝ) : ℂ) * φ x) -
      (𝔼 x ∈ s, ((D x * b x : ℝ) : ℂ) * φ x)‖ ≤ ε * M :=
  (norm_weighted_density_mean_sub_le s D a b φ hD hφ hab).trans
    (mul_le_mul_of_nonneg_left hM hε)

theorem masked_density_replacement_error {X : Type*} (s : Finset X)
    (D m a b : X → ℝ) (φ : X → ℂ) {ε G : ℝ} (hG : 0 ≤ G)
    (hD : ∀ x ∈ s, 0 ≤ D x) (hm : ∀ x ∈ s, |m x| ≤ G)
    (hφ : ∀ x ∈ s, ‖φ x‖ ≤ 1) (hab : ∀ x ∈ s, |a x - b x| ≤ ε) :
    ‖(𝔼 x ∈ s, ((D x * (m x * a x) : ℝ) : ℂ) * φ x) -
      (𝔼 x ∈ s, ((D x * (m x * b x) : ℝ) : ℂ) * φ x)‖ ≤
        (G * ε) * (𝔼 x ∈ s, D x) := by
  apply norm_weighted_density_mean_sub_le s D _ _ φ hD hφ
  intro x hx
  rw [← mul_sub, abs_mul]
  exact mul_le_mul (hm x hx) (hab x hx) (abs_nonneg _) hG

end Erdos3


namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem normalizedSpatial_probability_comparison {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (C : Matrix I N ℤ)
    (S P : I → ℝ) (T : J → ℝ) (Q : N → ℝ)
    (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hFree : ∀ j, 0 < Sum.elim T Q j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (g : (N → ℝ) → ℝ)
    (hf0 : ∀ p, 0 ≤ f p) (hg0 : ∀ n, 0 ≤ g n)
    {K Kfull : ℝ≥0} (hf : LipschitzWith K f) (hg : Continuous g)
    (hfull : LipschitzWith Kfull (splitFreeProfile f g))
    {R Rn δ G U V D L ρ H : ℝ} (h : ℕ)
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hscaleS : ∀ i, ρ ≤ S i) (hscaleFree : ∀ j, ρ ≤ Sum.elim T Q j)
    (hsmall : (A.det.natAbs : ℝ) ≤ ρ) (hcoeff : ∀ i j, |(A i j : ℝ)| ≤ D * L ^ h)
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, Rn < ‖n‖ → g n = 0)
    (hfmass : (∫ p, f p) = 1) (hgmass : (∫ n, g n) = 1)
    (hsmallMass : (2 * max R Rn + 2) ^ (Fintype.card I + Fintype.card (J ⊕ N)) * Kfull *
      ((A.det.natAbs : ℝ) / ρ) ≤ 1 / 2)
    (hbound : ∀ p, ‖splitFreeProfile f g p‖ ≤ H)
    (hindex : ((pivotFullImage A (Matrix.fromCols B C)).toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns (Matrix.fromCols B C) (Sum.elim T Q) P)‖ ≤ V)
    (hmove : ∀ n, g n ≠ 0 → ‖matrixSupCLM (normalizedIntegerColumns C Q P) n‖ ≤ δ) :
    ∃ hM : 0 < scaledInputMass (splitFreeProfile f g) S (Sum.elim T Q),
      let p := integerImagePMF A (Matrix.fromCols B C) (splitFreeProfile f g)
        (splitFreeProfile_nonneg hf0 hg0) S (Sum.elim T Q) hS hFree
        (splitFreeProfile_zero_outside hfs hgs) hM
      let w := maskedIntegerImageDensity A (Matrix.fromCols B C) P
        (normalizedFiberDensity A hA B S P T hS hP f)
      let E := (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card (J ⊕ N))
          G U V (max R Rn) H Kfull * ((Fintype.card I).factorial * D ^ Fintype.card I)) *
          L ^ (h * Fintype.card I) / ρ +
        G * (spatialKernelErrorConstant (Fintype.card I) (Fintype.card J) U R K * δ)
      (∀ v, |(∏ i, P i) * (p v).toReal - w v| ≤ E) ∧
      (∀ (s : Finset (I → ℤ)) (weight : (I → ℤ) → ℝ) (φ : (I → ℤ) → ℂ),
        (∀ v ∈ s, 0 ≤ weight v) → (∀ v ∈ s, ‖φ v‖ ≤ 1) →
        ‖(𝔼 v ∈ s, ((weight v * ((∏ i, P i) * (p v).toReal) : ℝ) : ℂ) * φ v) -
          (𝔼 v ∈ s, ((weight v * w v : ℝ) : ℂ) * φ v)‖ ≤ E * (𝔼 v ∈ s, weight v)) := by
  have hmass : (∫ p, splitFreeProfile f g p) = 1 := by
    rw [splitFreeProfile_integral hf.continuous hg hfs hgs, hfmass, hgmass, one_mul]
  obtain ⟨hM, hdiscrete⟩ := normalizedIntegerImage_polynomial_error A hA (Matrix.fromCols B C)
    S P (Sum.elim T Q) hS hP hFree (splitFreeProfile f g) (splitFreeProfile_nonneg hf0 hg0)
    hfull h (hR.trans (le_max_left _ _)) hρ hH hscaleS hscaleFree hsmall hcoeff
    (splitFreeProfile_zero_outside hfs hgs) hmass hsmallMass hbound hindex hinv hcol
  refine ⟨hM, ?_⟩
  dsimp only
  have hU : 0 ≤ U := (norm_nonneg _).trans hinv
  have hreal := normalizedSplitDensity_displacement A hA B C S P T Q hS hP
    hf hg hR hδ hfs hgs hg0 hgmass hinv hmove
  have hmasked := maskedIntegerImageDensity_error A (Matrix.fromCols B C) P
    (normalizedFiberDensity A hA (Matrix.fromCols B C) S P (Sum.elim T Q) hS hP (splitFreeProfile f g))
    (normalizedFiberDensity A hA B S P T hS hP f)
    (mul_nonneg (spatialKernelErrorConstant_nonneg _ _ K hU hR) hδ) hindex hreal
  have hpoint (v : I → ℤ) := (abs_sub_le
    ((∏ i, P i) * (integerImagePMF A (Matrix.fromCols B C) (splitFreeProfile f g)
      (splitFreeProfile_nonneg hf0 hg0) S (Sum.elim T Q) hS hFree
      (splitFreeProfile_zero_outside hfs hgs) hM v).toReal)
    (maskedIntegerImageDensity A (Matrix.fromCols B C) P
      (normalizedFiberDensity A hA (Matrix.fromCols B C) S P (Sum.elim T Q) hS hP
        (splitFreeProfile f g)) v)
    (maskedIntegerImageDensity A (Matrix.fromCols B C) P
      (normalizedFiberDensity A hA B S P T hS hP f) v)).trans
        (add_le_add (hdiscrete v) (hmasked v))
  refine ⟨hpoint, ?_⟩
  intro s weight φ hw hφ
  exact norm_weighted_density_mean_sub_le s weight _ _ φ hw hφ (fun v _ => hpoint v)

end Erdos3

end OAI
