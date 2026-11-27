import GRHArticle.ProgressionFree.NumberFieldIdeals.DensityExtrema
import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealRoughPasting
import GRHArticle.ProgressionFree.NumberFieldIdeals.SmoothOptimization
import GRHArticle.ProgressionFree.NumberFieldIdeals.SquarefreeExterior

/-!
# Lower bound for the extremal upper density of ideals

A single pasted ideal set realizes every stage of a finite weighted sum.
Letting the number of retained budgets grow gives the product of the
separately optimized value and the exterior squarefree factor.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset Filter Topology
open scoped nonZeroDivisors BigOperators

variable {K : Type*} [Field K] [NumberField K]

private theorem fixedBudgets_le_idealUpperDensitySupremum (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (M : ℕ)
    {Q : Set (Ideal (𝓞 K))⁰} {d : ℝ} (hQ : Q ⊆ roughIdeals S)
    (hQsf : ∀ g ∈ Q, ∀ p ∉ S, primeExponent p g ≤ 1) (hD : HasNaturalDensity Q d) :
    d * (∑ k ∈ Icc 1 M, (idealSmoothPrefixMaximum integral S k : ℝ) * integerPrefixStepWeight k) ≤
      idealUpperDensitySupremum K integral := by
  classical
  choose F hF hfF hFc using exists_idealSmoothPrefixOptimizer integral S
  let X := idealRoughPastingCutoff M
  let E := idealRoughPastedSet (K := K) M Q (fun k ↦ (F k : Set (Ideal (𝓞 K))⁰))
  have hE : IdealAdmissible integral E := idealAdmissible_idealRoughPastedSet integral S M hQ hQsf _
    (fun k _ ha ↦ (hF k ha).1) hfF
  let f (j : ℕ) : ℝ := ∑ k ∈ Icc 1 M,
    (((idealRoughBudgetBand Q (X j) k).ncard : ℝ) / countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) (X j)) *
      (F k).card
  have hf : Tendsto f atTop (𝓝 (d * ∑ k ∈ Icc 1 M,
      (idealSmoothPrefixMaximum integral S k : ℝ) * integerPrefixStepWeight k)) := by
    rw [mul_sum]
    apply tendsto_finsetSum
    intro k hk
    have hkp := (mem_Icc.mp hk).1
    simpa only [X, hFc, Function.comp_apply, mul_assoc, mul_comm (integerPrefixStepWeight k)] using
      ((tendsto_idealRoughBudgetBand_ncard_div hD hkp).comp (tendsto_idealRoughPastingCutoff M)).mul_const
        ((F k).card : ℝ)
  have hle (j : ℕ) : f j ≤ densityUpTo E (X j) := by
    have hcard := countUpTo_idealRoughPastedSet_ge S M j hQ F hF
    calc
      f j = ((∑ k ∈ Icc 1 M, (idealRoughBudgetBand Q (X j) k).ncard * (F k).card : ℕ) : ℝ) /
          countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) (X j) := by
        simp only [f, Nat.cast_sum, Nat.cast_mul, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k _
        rw [div_mul_eq_mul_div]
      _ ≤ densityUpTo E (X j) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact_mod_cast hcard
  exact (le_idealUpperDensity_of_tendsto_le (tendsto_idealRoughPastingCutoff M) hf
    (Eventually.of_forall hle)).trans (le_idealUpperDensitySupremum hE)

/-- Any squarefree rough family of known natural density realizes the
weighted budget sum as a lower bound on admissible upper density. -/
theorem squarefreeRoughWeightedSum_le_idealUpperDensitySupremum (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {Q : Set (Ideal (𝓞 K))⁰} {d : ℝ}
    (hQ : Q ⊆ roughIdeals S) (hQsf : ∀ g ∈ Q, ∀ p ∉ S, primeExponent p g ≤ 1)
    (hD : HasNaturalDensity Q d) :
    d * (∑' k, (idealSmoothPrefixMaximum integral S k : ℝ) * integerPrefixStepWeight k) ≤
      idealUpperDensitySupremum K integral := by
  let f (k : ℕ) := (idealSmoothPrefixMaximum integral S k : ℝ) * integerPrefixStepWeight k
  have hzero : f 0 = 0 := by simp [f, integerPrefixStepWeight]
  have hsum (M : ℕ) : ∑ k ∈ Icc 1 M, f k = ∑ k ∈ range (M+1), f k := by
    apply sum_subset
    · intro k hk
      exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hk).2)
    · intro k hk hnot
      have h : k = 0 := by
        by_contra hn
        exact hnot (mem_Icc.mpr ⟨Nat.pos_of_ne_zero hn, Nat.le_of_lt_succ (mem_range.mp hk)⟩)
      simpa only [h] using hzero
  have hlim : Tendsto (fun M ↦ d * ∑ k ∈ Icc 1 M, f k) atTop (𝓝 (d * ∑' k, f k)) := by
    simp_rw [hsum]
    exact tendsto_const_nhds.mul ((summable_idealSmoothPrefixMaximum integral S).hasSum.tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1))
  exact le_of_tendsto hlim (Eventually.of_forall fun M ↦
    fixedBudgets_le_idealUpperDensitySupremum integral S M hQ hQsf hD)

/-- The squarefree exterior factor times the normalized smooth upper
optimization is a lower bound for the true extremal upper density. -/
theorem idealSquarefreeExteriorFactor_mul_smoothUpper_le_upperDensitySupremum
    (integral : Bool) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    idealSquarefreeExteriorFactor S * idealSmoothUpperOptimization integral S ≤
      idealUpperDensitySupremum K integral := by
  have hQ : squarefreeRoughIdeals S ⊆ roughIdeals S := fun _ h ↦ h.1
  have hsf : ∀ g ∈ squarefreeRoughIdeals S, ∀ p ∉ S, primeExponent p g ≤ 1 := by
    intro g hg p hp
    have h := hg.2 p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    omega
  simpa only [idealSmoothUpperOptimization, idealSmoothDensityFactor, mul_assoc, mul_left_comm] using
    squarefreeRoughWeightedSum_le_idealUpperDensitySupremum integral S hQ hsf
      (hasNaturalDensity_squarefreeRoughIdeals S)

end GRHArticle.ProgressionFree.NumberFieldIdeals
