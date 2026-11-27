import GRHArticle.ProgressionFree.IntegerUpperDensityUpperBound
import GRHArticle.ProgressionFree.IntegerNaturalDensityComputability

/-!
# Computing the extremal integer upper densities

The finite comparison set contains exactly the smooth cutoffs where an
exhaustive cardinality optimization increases. Its missing reciprocal weight
is bounded by the full smooth tail, which has a rational error test.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

private def integerFiniteSmoothPrefixCount (integral : Bool) (Y k : ℕ) : ℕ :=
  (integerFiniteTemplateCandidates integral Y (k+1)).sup Finset.card

private theorem integerFiniteSmoothPool_succ_eq_prefixSlice (Y k : ℕ) :
    integerFiniteSmoothPool Y (k+1) = integerPrefixSlice (Nat.smoothNumbers (Y+1)) k := by
  ext n
  simp only [integerFiniteSmoothPool, integerPrefixSlice, mem_filter, mem_range, integerPrefix, mem_Icc]
  exact ⟨fun ⟨hn, hs⟩ ↦ ⟨⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hs), Nat.lt_succ_iff.mp hn⟩,hs⟩,
    fun ⟨⟨_,hn⟩,hs⟩ ↦ ⟨Nat.lt_succ_iff.mpr hn, hs⟩⟩

private theorem integerFiniteSmoothPrefixCount_eq (integral : Bool) (Y k : ℕ) :
    integerFiniteSmoothPrefixCount integral Y k = integerSmoothPrefixMaximum integral Y k := by
  classical
  have h : integerFiniteTemplateCandidates integral Y (k+1) =
      ((integerPrefixSlice (Nat.smoothNumbers (Y+1)) k).powerset.filter
        fun A : Finset ℕ ↦ IntegerPrefixAdmissible integral (A : Set ℕ)) := by
    ext A
    simp only [mem_integerFiniteTemplateCandidates, mem_filter, mem_powerset,
      integerFiniteSmoothPool_succ_eq_prefixSlice]
  rw [integerFiniteSmoothPrefixCount, integerSmoothPrefixMaximum, h]

/-- The finite jump set below `H`, computed by cardinality maximization. -/
def integerFiniteUpperJumpPool (integral : Bool) (Y H : ℕ) : Finset ℕ :=
  (integerFiniteSmoothPool Y H).filter (fun n ↦ integerFiniteSmoothPrefixCount integral Y (n-1) <
    integerFiniteSmoothPrefixCount integral Y n)

private theorem mem_integerFiniteUpperJumpPool {integral : Bool} {Y H n : ℕ} :
    n ∈ integerFiniteUpperJumpPool integral Y H ↔
      n ∈ integerFiniteSmoothPool Y H ∧ n ∈ integerSmoothPrefixJumps integral Y := by
  simp only [integerFiniteUpperJumpPool, mem_filter, integerFiniteSmoothPrefixCount_eq,
    integerSmoothPrefixJumps, Set.mem_setOf_eq]

/-- The finite rational approximation to the smooth upper optimization. -/
def integerFiniteUpperTemplateApprox (integral : Bool) (Y H : ℕ) : ℚ :=
  integerRoughDensityRat Y * integerTemplateWeightRat (integerFiniteUpperJumpPool integral Y H)

/-- The finite cardinal optimizations and the omitted smooth tail bound `U_Y`
from below and above. -/
theorem integerFiniteUpperTemplateApprox_bounds (integral : Bool) (Y H : ℕ) :
    let a : ℝ := integerFiniteUpperTemplateApprox integral Y H
    a ≤ integerSmoothUpperOptimization integral Y ∧
      integerSmoothUpperOptimization integral Y ≤ a + (integerTemplateTruncationError Y H : ℝ) := by
  classical
  let D := integerSmoothPrefixJumps integral Y
  let V := integerFiniteSmoothPool Y H
  let F := integerFiniteUpperJumpPool integral Y H
  let c := integerSmoothDensityFactor Y
  let w (n : ℕ) := (n:ℝ)⁻¹
  have hD : D ⊆ Nat.smoothNumbers (Y+1) := integerSmoothPrefixJumps_subset_smoothNumbers integral Y
  have hFV : F ⊆ V := fun n hn ↦ (mem_integerFiniteUpperJumpPool.mp hn).1
  have hFD : (F : Set ℕ) ⊆ D := fun n hn ↦ (mem_integerFiniteUpperJumpPool.mp hn).2
  have hV (n : ℕ) (hn : n ∈ V) : n ∈ Nat.smoothNumbers (Y+1) := (mem_filter.mp hn).2
  have hc : 0 < c := integerSmoothDensityFactor_pos Y
  let e : D → Nat.smoothNumbers (Y+1) := fun n ↦ ⟨n.val,hD n.property⟩
  have he : Function.Injective e := fun _ _ h ↦ Subtype.ext (congrArg
    (fun n : Nat.smoothNumbers (Y+1) ↦ n.val) h)
  have hs : Summable (fun n : D ↦ w n.val) := by
    simpa only [Function.comp_def, e, w] using (summable_reciprocal_smoothNumbers Y).comp_injective he
  have hlower : ∑ n ∈ F, w n ≤ ∑' n : D, w n.val := by
    have hi : Summable (D.indicator w) := summable_subtype_iff_indicator.mp hs
    have h := hi.sum_le_tsum F (fun n _ ↦ Set.indicator_nonneg (fun _ _ ↦ by dsimp [w]; positivity) _)
    have hF : ∑ n ∈ F, D.indicator w n = ∑ n ∈ F, w n :=
      Finset.sum_congr rfl (fun n hn ↦ Set.indicator_of_mem (hFD hn) w)
    rwa [hF, ← _root_.tsum_subtype D w] at h
  have hupper : (∑' n : D, w n.val) ≤ (∑ n ∈ F, w n) + (c⁻¹ - ∑ n ∈ V, w n) := by
    have h := smooth_reciprocal_add_omitted_le hD (V \ F) (by
      intro n hn
      obtain ⟨hnV,hnF⟩ := mem_sdiff.mp hn
      exact ⟨hV n hnV, fun hnD ↦ hnF (mem_integerFiniteUpperJumpPool.mpr ⟨hnV,hnD⟩)⟩)
    have hs := Finset.sum_sdiff hFV (f := w)
    change (∑' n : D, w n.val) + ∑ n ∈ V \ F, w n ≤ c⁻¹ at h
    linarith only [h,hs]
  dsimp only
  simp only [integerFiniteUpperTemplateApprox, integerTemplateTruncationError, Rat.cast_sub, Rat.cast_one,
    Rat.cast_mul, cast_integerRoughDensityRat, cast_integerTemplateWeightRat,
    integerSmoothUpperOptimization_eq_jump_reciprocal]
  change c * (∑ n ∈ F, w n) ≤ c * (∑' n : D, w n.val) ∧
    c * (∑' n : D, w n.val) ≤ c * (∑ n ∈ F, w n) + (1 - c * ∑ n ∈ V, w n)
  refine ⟨mul_le_mul_of_nonneg_left hlower hc.le, ?_⟩
  have h := mul_le_mul_of_nonneg_left hupper hc.le
  rwa [mul_add, mul_sub, mul_inv_cancel₀ hc.ne'] at h

/-- Rational approximation to the extremal upper density at dyadic precision. -/
def integerUpperDensityApprox (integral : Bool) (k : ℕ) : ℚ :=
  let Y := 2^(k+1)
  integerFiniteUpperTemplateApprox integral Y (integerTemplateCutoff Y k)

/-- The algorithm approximates the extremal upper density with dyadic error
for both ratio conventions. -/
theorem integerUpperDensityApprox_error (integral : Bool) (k : ℕ) :
    |(integerUpperDensityApprox integral k : ℝ) - integerUpperDensitySupremum integral| ≤
      (1/2:ℝ)^(k+1) := by
  let Y : ℕ := 2^(k+1)
  let H := integerTemplateCutoff Y k
  have ht : integerTemplateTruncationError Y H ≤ (1/2:ℚ)^(k+1) := integerTemplateCutoff_spec Y k
  have hreal := (Rat.cast_le (K := ℝ)).mpr ht
  simp only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hreal
  obtain ⟨ha,hb⟩ := integerFiniteUpperTemplateApprox_bounds integral Y H
  have hc := integerUpperDensitySupremum_le_smoothUpperOptimization integral Y
  have hd := integerSmoothUpperOptimization_sub_integerPrimeSquareTail_le_integerUpperDensitySupremum integral Y
  have he := integerPrimeSquareTail_le_reciprocal (Y := Y) (by dsimp [Y]; positivity)
  have hdy : 1/(Y:ℝ) = (1/2:ℝ)^(k+1) := by simp [Y]
  rw [hdy] at he
  change |(integerFiniteUpperTemplateApprox integral Y H : ℝ) - _| ≤ _
  apply abs_le.mpr
  constructor <;> linarith only [ha,hb,hc,hd,he,hreal]

end GRHArticle.ProgressionFree
