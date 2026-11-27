import GRHArticle.ProgressionFree.BoundedPrimeBlockConvergence
import GRHArticle.ProgressionFree.FiniteLengthProgressionTest
import GRHArticle.ProgressionFree.IntegerNaturalDensityComputability

/-!
# Computable unrestricted natural-density optima at arbitrary lengths

The same rational smooth cutoff test works for every length. For a finite
smooth pool, enumerate all subsets and apply the executable finite
progression test. The omitted smooth mass and the prime-power tail
certify the resulting approximation.
-/

namespace GRHArticle.ProgressionFree

open Finset

/-- The finite candidates for the smooth optimization at length `k`. -/
def integerLengthFiniteTemplateCandidates (k Y H : ℕ) : Finset (Finset ℕ) :=
  (integerFiniteSmoothPool Y H).powerset.filter (fun A ↦ finiteLengthGPTest k A = true)

private theorem lengthCandidates_nonempty (k Y H : ℕ) :
    (integerLengthFiniteTemplateCandidates k Y H).Nonempty :=
  ⟨∅,by simp [integerLengthFiniteTemplateCandidates,finiteLengthGPTest]⟩

theorem mem_integerLengthFiniteTemplateCandidates {k Y H : ℕ} {A : Finset ℕ} (hk : 2 ≤ k) :
    A ∈ integerLengthFiniteTemplateCandidates k Y H ↔
      A ⊆ integerFiniteSmoothPool Y H ∧ KTermGPFree k (A : Set ℕ) := by
  simp only [integerLengthFiniteTemplateCandidates,mem_filter,mem_powerset,finiteLengthGPTest_spec hk]

/-- The rational weighted optimum over the finite smooth pool. -/
def integerLengthFiniteTemplateApprox (k Y H : ℕ) : ℚ :=
  integerRoughDensityRat Y * (integerLengthFiniteTemplateCandidates k Y H).sup'
    (lengthCandidates_nonempty k Y H) integerTemplateWeightRat

/-- The finite search bounds the infinite smooth optimization with exactly
the pre-existing rational truncation error. -/
theorem integerLengthFiniteTemplateApprox_bounds {k : ℕ} (hk : 2 ≤ k) (Y H : ℕ) :
    let a : ℝ := integerLengthFiniteTemplateApprox k Y H
    a ≤ integerLengthSmoothOptimization k Y ∧
      integerLengthSmoothOptimization k Y ≤ a + (integerTemplateTruncationError Y H : ℝ) := by
  classical
  let V := integerFiniteSmoothPool Y H
  let C := integerLengthFiniteTemplateCandidates k Y H
  let m := C.sup' (lengthCandidates_nonempty k Y H) integerTemplateWeightRat
  let W := integerLengthSmoothTemplateWeights k Y
  let c := integerSmoothDensityFactor Y
  have hV (s : ℕ) (hs : s ∈ V) : s ∈ Nat.smoothNumbers (Y+1) := (mem_filter.mp hs).2
  have hc : 0 < c := integerSmoothDensityFactor_pos _
  have hW : W.Nonempty := integerLengthSmoothTemplateWeights_nonempty (by omega) Y
  dsimp only
  simp only [integerLengthFiniteTemplateApprox,integerTemplateTruncationError,Rat.cast_sub,
    Rat.cast_one,Rat.cast_mul,cast_integerRoughDensityRat]
  change c*(m:ℝ) ≤ c*sSup W ∧ c*sSup W ≤
    c*(m:ℝ)+(1-c*(integerTemplateWeightRat V : ℝ))
  constructor
  · apply mul_le_mul_of_nonneg_left _ hc.le
    obtain ⟨A,hA,hm⟩ := exists_mem_eq_sup' (lengthCandidates_nonempty k Y H) integerTemplateWeightRat
    change m = integerTemplateWeightRat A at hm
    rw [hm,cast_integerTemplateWeightRat]
    obtain ⟨hsub,hfree⟩ := (mem_integerLengthFiniteTemplateCandidates hk).mp hA
    exact le_csSup (integerLengthSmoothTemplateWeights_bddAbove k Y)
      ⟨A,fun _ hs ↦ hV _ (hsub hs),hfree,(Finset.tsum_subtype A (fun s : ℕ ↦ (s:ℝ)⁻¹)).symm⟩
  · have hBound : sSup W ≤ (m:ℝ) + (c⁻¹-(integerTemplateWeightRat V : ℝ)) := by
      apply csSup_le hW
      rintro w ⟨A,hA,hfree,rfl⟩
      let S := V.filter (· ∈ A)
      have hSV : S ⊆ V := filter_subset _ _
      have hSC : S ∈ C := (mem_integerLengthFiniteTemplateCandidates hk).mpr
        ⟨hSV,hfree.mono fun x hx ↦ (mem_filter.mp hx).2⟩
      have hMax := (Rat.cast_le (K := ℝ)).mpr (le_sup' integerTemplateWeightRat hSC)
      change (integerTemplateWeightRat S : ℝ) ≤ (m : ℝ) at hMax
      have h := smooth_reciprocal_add_omitted_le hA (V \ S) (by
        intro n hn
        obtain ⟨hv,hs⟩ := mem_sdiff.mp hn
        exact ⟨hV n hv,fun hh ↦ hs (mem_filter.mpr ⟨hv,hh⟩)⟩)
      have he := Finset.sum_sdiff hSV (f := fun n : ℕ ↦ (n:ℝ)⁻¹)
      rw [cast_integerTemplateWeightRat] at hMax ⊢
      change _ ≤ c⁻¹ at h
      linarith only [h,hMax,he]
    have h := mul_le_mul_of_nonneg_left hBound hc.le
    rwa [mul_add,mul_sub,mul_inv_cancel₀ hc.ne'] at h

/-- A uniform executable rational approximation to the unrestricted
extremal natural density at a specified progression length. -/
def integerLengthNaturalDensityApprox (k precision : ℕ) : ℚ :=
  let Y := 2^(precision+1)
  integerLengthFiniteTemplateApprox k Y (integerTemplateCutoff Y precision)

/-- The approximation error is at most `2^(-(precision+1))` for every
length at least three. -/
theorem integerLengthNaturalDensityApprox_error {k : ℕ} (hk : 3 ≤ k) (precision : ℕ) :
    |(integerLengthNaturalDensityApprox k precision : ℝ) - integerLengthNaturalDensitySupremum k| ≤
      (1/2:ℝ)^(precision+1) := by
  let Y := 2^(precision+1)
  let H := integerTemplateCutoff Y precision
  let d := max 1 (Nat.primesLE Y).card
  have hY : 2 ≤ Y := by
    dsimp [Y]
    rw [pow_succ]
    exact Nat.le_mul_of_pos_left 2 (by positivity)
  have hWidth : (Nat.primesLE Y).card ≤ d := le_max_right _ _
  have hd : 0 < d := by have h : 1 ≤ d := le_max_left _ _; omega
  have hT := (Rat.cast_le (K := ℝ)).mpr (integerTemplateCutoff_spec Y precision)
  simp only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hT
  obtain ⟨hA,hB⟩ := integerLengthFiniteTemplateApprox_bounds (by omega : 2 ≤ k) Y H
  have hU := integerLengthNaturalDensitySupremum_le_smoothOptimization (by omega : 0 < k) Y
  have hLower := (integerLengthSmoothOptimization_sub_tail_le_boundedPrimeBlocks hk hY hd hWidth).trans
    (integerBoundedPrimeBlockDensitySupremum_lt_lengthNaturalDensitySupremum hk hd).le
  have hTail : 1 / (((k-2 : ℕ) : ℝ)*(Y : ℝ)^(k-2)) ≤ (1/2:ℝ)^(precision+1) := by
    have hEq : 1/(Y:ℝ) = (1/2:ℝ)^(precision+1) := by simp [Y]
    rw [← hEq]
    have hYr : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
    apply one_div_le_one_div_of_le hYr
    have hm : (1 : ℝ) ≤ ((k-2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k-2 by omega)
    have hp : (Y:ℝ) ≤ (Y:ℝ)^(k-2) :=
      le_self_pow₀ (by exact_mod_cast (show 1 ≤ Y by omega)) (by omega)
    exact hp.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hm (pow_nonneg hYr.le _))
  change |(integerLengthFiniteTemplateApprox k Y H : ℝ) - _| ≤ _
  apply abs_le.mpr
  constructor <;> linarith only [hA,hB,hU,hT,hLower,hTail]

end GRHArticle.ProgressionFree
