import GRHArticle.ProgressionFree.IntegerNaturalDensityApproximation
import GRHArticle.ProgressionFree.IntegerSmoothPacking

/-!
# Computing the fixed smooth optimization on a finite interval

Enumerate the admissible subsets of the smooth numbers less than `H` and
maximize their reciprocal weight. The missing smooth mass gives a rational
error bound independent of the choice of admissible template.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped BigOperators

/-- The rational form of the finite rough-density Euler factor. -/
def integerRoughDensityRat (Y : ℕ) : ℚ := ∏ p ∈ Nat.primesLE Y, (1-(p:ℚ)⁻¹)

theorem cast_integerRoughDensityRat (Y : ℕ) :
    (integerRoughDensityRat Y : ℝ) = integerSmoothDensityFactor Y := by
  simp [integerRoughDensityRat, integerSmoothDensityFactor]

def integerFiniteSmoothPool (Y H : ℕ) : Finset ℕ :=
  (range H).filter (fun s ↦ s ∈ Nat.smoothNumbers (Y+1))

def integerTemplateWeightRat (S : Finset ℕ) : ℚ := ∑ s ∈ S, (s:ℚ)⁻¹

theorem cast_integerTemplateWeightRat (S : Finset ℕ) :
    (integerTemplateWeightRat S : ℝ) = ∑ s ∈ S, (s:ℝ)⁻¹ := by simp [integerTemplateWeightRat]

private def test (integral : Bool) (A : Finset ℕ) : Bool :=
  decide (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < b → b < c → a*c = b*b →
    (integral = true → a ∣ b) → False)

private theorem test_spec {integral : Bool} {A : Finset ℕ} :
    test integral A = true ↔ IntegerPrefixAdmissible integral (A : Set ℕ) := by
  simp only [test, decide_eq_true_eq]
  exact ⟨fun h _ _ _ ha hb hc ↦ h _ ha _ hb _ hc,fun h _ ha _ hb _ hc ↦ h ha hb hc⟩

/-- All admissible subsets of the smooth numbers below the cutoff. -/
def integerFiniteTemplateCandidates (integral : Bool) (Y H : ℕ) : Finset (Finset ℕ) :=
  (integerFiniteSmoothPool Y H).powerset.filter (fun A ↦ test integral A = true)

theorem mem_integerFiniteTemplateCandidates {integral : Bool} {Y H : ℕ} {A : Finset ℕ} :
    A ∈ integerFiniteTemplateCandidates integral Y H ↔
      A ⊆ integerFiniteSmoothPool Y H ∧ IntegerPrefixAdmissible integral (A : Set ℕ) := by
  simp only [integerFiniteTemplateCandidates, mem_filter, mem_powerset, test_spec]

private theorem candidates_nonempty (integral : Bool) (Y H : ℕ) :
    (integerFiniteTemplateCandidates integral Y H).Nonempty :=
  ⟨∅,mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),test_spec.mpr (by
    intro a b c ha; exact (Finset.notMem_empty a ha).elim)⟩⟩

/-- The exact finite weighted optimum, calculated over a finite powerset. -/
def integerFiniteTemplateApprox (integral : Bool) (Y H : ℕ) : ℚ :=
  integerRoughDensityRat Y * (integerFiniteTemplateCandidates integral Y H).sup' (candidates_nonempty integral Y H) integerTemplateWeightRat

/-- Computable upper bound on the weight missed beyond the cutoff. -/
def integerTemplateTruncationError (Y H : ℕ) : ℚ :=
  1-integerRoughDensityRat Y * integerTemplateWeightRat (integerFiniteSmoothPool Y H)

/-- The true smooth optimization lies in an interval with rational endpoints. -/
theorem integerFiniteTemplateApprox_bounds (integral : Bool) (Y H : ℕ) :
    let a : ℝ := integerFiniteTemplateApprox integral Y H
    a ≤ integerSmoothLowerOptimization integral Y ∧
      integerSmoothLowerOptimization integral Y ≤ a + (integerTemplateTruncationError Y H : ℝ) := by
  classical
  let V := integerFiniteSmoothPool Y H
  let C := integerFiniteTemplateCandidates integral Y H
  let m := C.sup' (candidates_nonempty integral Y H) integerTemplateWeightRat
  let c := integerSmoothDensityFactor Y
  let W : Set ℝ := {w | ∃ S : Set ℕ, S ⊆ Nat.smoothNumbers (Y+1) ∧
    IntegerPrefixAdmissible integral S ∧ w = ∑' s : S, (s.val : ℝ)⁻¹}
  have hV {s : ℕ} (hs : s ∈ V) := (mem_filter.mp hs).2
  have hc : 0 < c := integerSmoothDensityFactor_pos Y
  have hW : W.Nonempty := ⟨_,∅,Set.empty_subset _,by intro a b c ha; exact ha.elim,rfl⟩
  have hC : BddAbove W := by
    refine ⟨c⁻¹, ?_⟩
    rintro _ ⟨S,hS,_,rfl⟩
    exact smoothSubset_reciprocal_le hS
  dsimp only
  simp only [integerFiniteTemplateApprox, integerTemplateTruncationError, Rat.cast_sub, Rat.cast_one,
    Rat.cast_mul,cast_integerRoughDensityRat]
  change c * (m:ℝ) ≤ c * sSup W ∧ c * sSup W ≤ c * (m:ℝ) + (1 - c * (integerTemplateWeightRat V : ℝ))
  constructor
  · apply mul_le_mul_of_nonneg_left _ hc.le
    obtain ⟨A,hA,hm⟩ := exists_mem_eq_sup' (candidates_nonempty integral Y H) integerTemplateWeightRat
    change m = integerTemplateWeightRat A at hm
    rw [hm, cast_integerTemplateWeightRat]
    apply le_csSup hC
    refine ⟨A,fun _ hs ↦ hV ((mem_powerset.mp (mem_filter.mp hA).1) hs),test_spec.mp (mem_filter.mp hA).2,?_⟩
    exact (Finset.tsum_subtype A (fun s : ℕ ↦ (s:ℝ)⁻¹)).symm
  · have hUpper : sSup W ≤ (m:ℝ) + (c⁻¹ - (integerTemplateWeightRat V : ℝ)) := by
      apply csSup_le hW
      rintro _ ⟨S,hS,ha,rfl⟩
      let A := V.filter (· ∈ S)
      have hAV : A ⊆ V := filter_subset _ _
      have hA : A ∈ C := mem_filter.mpr ⟨mem_powerset.mpr hAV,test_spec.mpr
        (fun _ _ _ hx hy hz ↦ ha (mem_filter.mp hx).2 (mem_filter.mp hy).2 (mem_filter.mp hz).2)⟩
      have hmax := (Rat.cast_le (K := ℝ)).mpr (Finset.le_sup' integerTemplateWeightRat hA)
      change (integerTemplateWeightRat A : ℝ) ≤ (m : ℝ) at hmax
      have h := smooth_reciprocal_add_omitted_le hS (V \ A) (by
        intro n hn
        obtain ⟨hv,he⟩ := mem_sdiff.mp hn
        exact ⟨hV hv,fun hs ↦ he (mem_filter.mpr ⟨hv,hs⟩)⟩)
      have he := Finset.sum_sdiff hAV (f := fun n : ℕ ↦ (n:ℝ)⁻¹)
      rw [cast_integerTemplateWeightRat] at hmax ⊢
      change _ ≤ c⁻¹ at h
      linarith only [h,hmax,he]
    have h := mul_le_mul_of_nonneg_left hUpper hc.le
    rwa [mul_add, mul_sub, mul_inv_cancel₀ hc.ne'] at h

/-- The explicit error test eventually succeeds at every positive tolerance. -/
theorem tendsto_integerTemplateTruncationError (Y : ℕ) :
    Tendsto (fun H ↦ (integerTemplateTruncationError Y H : ℝ)) atTop (𝓝 0) := by
  let S := Nat.smoothNumbers (Y+1)
  let w (s : ℕ) := (s:ℝ)⁻¹
  have hs : HasSum (S.indicator w) (integerSmoothDensityFactor Y)⁻¹ := by
    have ht : Summable (S.indicator w) := summable_subtype_iff_indicator.mp (summable_reciprocal_smoothNumbers Y)
    rw [← (hasSum_reciprocal_smoothNumbers Y).tsum_eq, _root_.tsum_subtype S w]
    exact ht.hasSum
  have h := (tendsto_const_nhds (x := (1:ℝ))).sub (hs.tendsto_sum_nat.const_mul (integerSmoothDensityFactor Y))
  rw [mul_inv_cancel₀ (integerSmoothDensityFactor_pos Y).ne',sub_self] at h
  refine h.congr fun H ↦ ?_
  simp only [integerTemplateTruncationError, Rat.cast_sub, Rat.cast_one, Rat.cast_mul,
    cast_integerRoughDensityRat, cast_integerTemplateWeightRat,integerFiniteSmoothPool, Finset.sum_filter]
  simp only [Set.indicator_apply, S, w]

end GRHArticle.ProgressionFree
