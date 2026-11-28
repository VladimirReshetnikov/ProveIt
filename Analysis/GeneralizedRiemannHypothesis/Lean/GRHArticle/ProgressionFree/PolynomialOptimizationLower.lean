import GRHArticle.ProgressionFree.PolynomialSquarefreeOptimalBall
import GRHArticle.ProgressionFree.PolynomialRoughWeightLimit
import GRHArticle.ProgressionFree.PolynomialEulerTail
import GRHArticle.ProgressionFree.PolynomialSupremum

/-!
# The lower finite-prime approximation for polynomial-ratio density

The finite squarefree selections have a limiting proportion computed by a
rough-count convolution. Gluing their upper degree blocks puts the limiting
proportion below the supremum over single progression-free sets.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology
open scoped BigOperators

private theorem roughDensity_eq_ratio_mul (F : Type*) [Field F] [Fintype F] (T : ℕ) :
    polynomialRoughDensity F T = polynomialSquarefreeRoughRatio F T *
      ∏ p ∈ polynomialSmoothPrimes F T, (1 - (Fintype.card F : ℝ)⁻¹ ^ p.natDegree) := by
  let S := polynomialSmoothPrimes F T
  let z := (Fintype.card F : ℝ)⁻¹
  have hq : 1 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hz₀ : 0 ≤ z := inv_nonneg.mpr (zero_lt_one.trans hq).le
  have hz₁ : z < 1 := inv_lt_one_of_one_lt₀ hq
  have hminus : 0 < ∏ p ∈ S, (1 - z ^ p.natDegree) := by
    apply Finset.prod_pos
    intro p hp
    exact sub_pos.mpr (pow_lt_one₀ hz₀ hz₁
      (mem_polynomialSmoothPrimes.mp hp).2.1.natDegree_pos.ne')
  have hplus : 0 < ∏ p ∈ S, (1 + z ^ p.natDegree) :=
    Finset.prod_pos fun p _ ↦ add_pos_of_pos_of_nonneg zero_lt_one (pow_nonneg hz₀ _)
  have hprod : (∏ p ∈ S, (1 - z ^ (2 * p.natDegree))) =
      (∏ p ∈ S, (1 - z ^ p.natDegree)) * (∏ p ∈ S, (1 + z ^ p.natDegree)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    rw [Nat.mul_comm 2, pow_mul]
    ring
  change (1 - z) * (∏ p ∈ S, (1 + z ^ p.natDegree)⁻¹) =
    (1 - z) / (∏ p ∈ S, (1 - z ^ (2 * p.natDegree))) * (∏ p ∈ S, (1 - z ^ p.natDegree))
  rw [hprod, Finset.prod_inv_distrib]
  field_simp [hminus.ne', hplus.ne']

/-- The finite progression-free squarefree-rough selections attain the lower
approximation in the limit of their ball proportions. -/
theorem tendsto_polynomialSquarefreeTemplateBall_proportion
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (T : ℕ) (H : ℕ → Finset (Polynomial F))
    (M : ℕ → ℕ) (hH : ∀ t, H t ⊆ polynomialSmoothBall F T t) (hM : ∀ t, (H t).card = M t)
    (hs : Summable (fun t ↦ (M t : ℝ) * (Fintype.card F : ℝ)⁻¹^t)) :
    Tendsto (fun N ↦ polynomialBallProportion (polynomialSquarefreeTemplateBall T N H) N) atTop
      (𝓝 (polynomialSquarefreeRoughRatio F T * polynomialDensityUpperWith F T M)) := by
  let q := (Fintype.card F : ℝ)
  let z := q⁻¹
  let w (t : ℕ) := (M t : ℝ) * z ^ t
  let r (n : ℕ) := ((polynomialSquarefreeRoughLayer F T n).card : ℝ) / q ^ n
  have hq : 0 < q := by
    dsimp only [q]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hr (n : ℕ) : r n ∈ Set.Icc 0 1 := by
    have hsub : polynomialSquarefreeRoughLayer F T n ⊆ monicLayer F n :=
      fun f hf ↦ let h := mem_polynomialSquarefreeRoughLayer.mp hf
        mem_monicLayer.mpr ⟨h.1, h.2.1⟩
    have hcard : (polynomialSquarefreeRoughLayer F T n).card ≤ Fintype.card F ^ n :=
      (Finset.card_le_card hsub).trans_eq (card_monicLayer n)
    exact ⟨div_nonneg (Nat.cast_nonneg _) (pow_nonneg hq.le _),
      (div_le_one (pow_pos hq _)).2 (by dsimp only [q]; exact_mod_cast hcard)⟩
  have hlimit := tendsto_weighted_rough_convolution _ hs (fun _ ↦ by positivity) hr
    (tendsto_polynomialSquarefreeRoughLayer_card_div_pow F T)
  have hcount (N : ℕ) : polynomialBallProportion (polynomialSquarefreeTemplateBall T N H) N =
      (1 - z) * ∑ t ∈ Finset.range (N + 1), r (N - t) * w t := by
    unfold polynomialBallProportion
    rw [card_polynomialSquarefreeTemplateBall H T N hH]
    simp only [hM]
    simp only [mul_assoc]
    rw [← Finset.mul_sum]
    exact polynomial_weighted_convolution_scale F N
      (fun n ↦ (polynomialSquarefreeRoughLayer F T n).card) M
  have htarget : (1 - z) * (polynomialRoughDensity F T * ∑' t : ℕ, w t) =
      polynomialSquarefreeRoughRatio F T * polynomialDensityUpperWith F T M := by
    rw [roughDensity_eq_ratio_mul, polynomialDensityUpperWith]
    change (1 - z) * (polynomialSquarefreeRoughRatio F T *
      (∏ p ∈ polynomialSmoothPrimes F T, (1 - z ^ p.natDegree)) * ∑' t : ℕ, w t) =
      polynomialSquarefreeRoughRatio F T * ((1 - z) *
        (∏ p ∈ polynomialSmoothPrimes F T, (1 - z ^ p.natDegree)) * ∑' t : ℕ, w t)
    ring
  rw [← htarget]
  exact (hlimit.const_mul (1 - z)).congr fun N ↦ (hcount N).symm

theorem tendsto_polynomialSquarefreeOptimalBall_proportion
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (T : ℕ) :
    Tendsto (fun N ↦ polynomialBallProportion (polynomialSquarefreeOptimalBall F T N) N) atTop
      (𝓝 (polynomialSquarefreeRoughRatio F T * polynomialDensityUpperApproximation F T)) :=
  tendsto_polynomialSquarefreeTemplateBall_proportion F T (polynomialSmoothOptimizer F T)
    (polynomialSmoothMaximum F T) (fun t ↦ (polynomialSmoothOptimizer_properties F T t).1)
    (fun t ↦ (polynomialSmoothOptimizer_properties F T t).2.2)
    (summable_polynomialSmoothMaximum_weight (F := F) T)

/-- The squarefree-corrected finite-prime approximation is below the supremum.
A single progression-free set witnesses this lower bound. -/
theorem polynomialSquarefreeRoughRatio_mul_upperApproximation_le_supremum
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (T : ℕ) :
    polynomialSquarefreeRoughRatio F T * polynomialDensityUpperApproximation F T ≤
      polynomialRatioDensitySupremum F := by
  let N := polynomialBlockCutoff 0
  let E (j : ℕ) := polynomialSquarefreeOptimalBall F T (N j)
  have hN := polynomialBlockCutoff_strictMono 0
  have hlimit := (tendsto_polynomialSquarefreeOptimalBall_proportion F T).comp hN.tendsto_atTop
  have hfree : PolynomialRatioThreeGPFree (polynomialBlockUnion N E) :=
    polynomialRatioThreeGPFree_blockUnion (fun _ _ h ↦ polynomialBlockCutoff_gap 0 h)
      (fun j ↦ polynomialSquarefreeOptimalBall_free T (N j))
  exact (polynomialBlockUnion_le_limsup hN E hlimit).trans (le_polynomialRatioDensitySupremum hfree)

end GRHArticle.ProgressionFree
