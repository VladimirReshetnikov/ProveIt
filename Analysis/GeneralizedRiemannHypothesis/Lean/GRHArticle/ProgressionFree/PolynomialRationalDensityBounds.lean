import GRHArticle.ProgressionFree.PolynomialRationalFibers
import GRHArticle.ProgressionFree.PolynomialOptimizationLower
import GRHArticle.ProgressionFree.PolynomialOptimizationBounds
import GRHArticle.ProgressionFree.PolynomialSmoothUpperBound

/-!
# Effective prime-cutoff bounds for rational-function progressions

For a finite field of order `q`, the actual supremum lies between `v_T U_T`
and `U_T`. The two endpoints differ by at most `q^(-(T+1))`. Independent
smooth optimizers can be used for each squarefree rough factor.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- Weighted series of exact rational-function smooth-ball maxima. -/
noncomputable def rationalFunctionDensityUpperApproximation (T : ℕ) : ℝ :=
  polynomialDensityUpperWith F T (rationalFunctionSmoothMaximum F T)

theorem summable_rationalFunctionSmoothMaximum_weight (T : ℕ) :
    Summable (fun t ↦ (rationalFunctionSmoothMaximum F T t : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ t) :=
  (summable_polynomialSmoothMaximum_weight (F := F) T).of_nonneg_of_le
    (fun _ ↦ by positivity) fun t ↦ mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (rationalFunctionSmoothMaximum_le_polynomialSmoothMaximum T t)) (by positivity)

theorem RationalFunctionRatioThreeGPFree.smoothFiberBound {E : Set F[X]}
    (hE : RationalFunctionRatioThreeGPFree E) (T : ℕ) :
    PolynomialSmoothFiberBound E T (rationalFunctionSmoothMaximum F T) := by
  intro t B z hB hmul
  have hB' : B ⊆ polynomialSmoothBall F T t := by
    have he := congrArg (fun de ↦ @polynomialSmoothBall F _ _ de T t)
      (Subsingleton.elim (Classical.decEq F) (inferInstance : DecidableEq F))
    exact he ▸ hB
  apply le_rationalFunctionSmoothMaximum hB'
  by_cases hz : z = 0
  · intro a b c _ _ _ ha
    exact ((hmul a ha).1 (by simp [hz])).elim
  · exact (hE.mul_preimage hz).mono (fun b hb ↦ (hmul b hb).2)

/-- Upper and lower cutoff comparisons for the rational-function convention. -/
theorem rationalFunctionRatioDensitySupremum_bounds (T : ℕ) :
    polynomialSquarefreeRoughRatio F T * rationalFunctionDensityUpperApproximation F T ≤
      rationalFunctionRatioDensitySupremum F ∧
    rationalFunctionRatioDensitySupremum F ≤ rationalFunctionDensityUpperApproximation F T := by
  have hs := summable_rationalFunctionSmoothMaximum_weight F T
  constructor
  · choose H hsub hfree hcard using exists_rationalFunctionSmoothMaximum (F := F) T
    let N := polynomialBlockCutoff 0
    let E (j : ℕ) := polynomialSquarefreeTemplateBall T (N j) H
    have hN := polynomialBlockCutoff_strictMono 0
    have hlimit := (tendsto_polynomialSquarefreeTemplateBall_proportion F T H _
      hsub hcard hs).comp hN.tendsto_atTop
    have hE (j : ℕ) : RationalFunctionRatioThreeGPFree (E j) :=
      (rationalFunctionRatioThreeGPFree_squarefreeFibers T
        (fun g ↦ (H (N j - g.natDegree) : Set F[X])) (fun _ ↦ hfree _)).mono
        fun _ hf ↦ ⟨hf.2.2.1, hf.2.2.2⟩
    have hu := rationalFunctionRatioThreeGPFree_blockUnion
      (fun _ _ h ↦ polynomialBlockCutoff_gap 0 h) hE
    exact (polynomialBlockUnion_le_limsup hN E hlimit).trans (le_polynomialBlockDensitySupremum hu)
  · obtain ⟨E, _, hE, he⟩ := rationalFunctionRatioDensitySupremum_attained (F := F)
    rw [← he]
    exact (hE.smoothFiberBound F T).limsup_le hs

theorem rationalFunctionDensityUpperApproximation_le_polynomial (T : ℕ) :
    rationalFunctionDensityUpperApproximation F T ≤ polynomialDensityUpperApproximation F T := by
  let z := (Fintype.card F : ℝ)⁻¹
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hz₁ : z ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos (α := F))
  unfold rationalFunctionDensityUpperApproximation polynomialDensityUpperApproximation polynomialDensityUpperWith
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sub_nonneg.mpr hz₁)
    (Finset.prod_nonneg fun p _ ↦ sub_nonneg.mpr (pow_le_one₀ hz hz₁)))
  exact (summable_rationalFunctionSmoothMaximum_weight F T).tsum_le_tsum (fun t ↦
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (rationalFunctionSmoothMaximum_le_polynomialSmoothMaximum T t))
      (pow_nonneg hz _)) (summable_polynomialSmoothMaximum_weight (F := F) T)

/-- The geometric tail improves the article's explicit cutoff error for
the rational-function supremum over every finite field. -/
theorem rationalFunctionDensityUpperApproximation_supremum_error (T : ℕ) :
    let U := rationalFunctionDensityUpperApproximation F T
    let β := rationalFunctionRatioDensitySupremum F
    let v := polynomialSquarefreeRoughRatio F T
    0 ≤ U - β ∧ U - β ≤ 1-v ∧ 1-v ≤ (Fintype.card F : ℝ)⁻¹^(T+1) := by
  obtain ⟨hl, hu⟩ := rationalFunctionRatioDensitySupremum_bounds F T
  have hv := polynomialSquarefreeRoughRatio_error F T
  have hU := (rationalFunctionDensityUpperApproximation_le_polynomial F T).trans
    (polynomialDensityUpperApproximation_mem_unitInterval F T).2
  refine ⟨sub_nonneg.mpr hu, ?_, hv.2⟩
  calc
    _ ≤ (1 - polynomialSquarefreeRoughRatio F T) * rationalFunctionDensityUpperApproximation F T := by
      linarith only [hl]
    _ ≤ _ := mul_le_of_le_one_right hv.1 hU

end GRHArticle.ProgressionFree
