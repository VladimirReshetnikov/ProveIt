import GRHArticle.ProgressionFree.IntegerPrefixTransfer

/-!
# The replacement set for McNew's Question 7.4
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

private def replacementValues : List ℕ :=
  [1,2,3,5,6,8,10,15,16,24,
   27,40,48,54,60,80,81,90,120,125,
   135,150,162,180,216,250,270,300,375,405,
   432,450,512,625,648,750,900,1000,1024,1080,
   1250,1296,1536,1875,2000,2560,3000,3072,3375,4096,
   5000,5120,6750,7680,8192,10000,10125,12288,13824,15360,
   16875,19683,20480,24576,27000,27648,39366,40960,41472,50625,
   59049,61440,64000,69120,82944,98415,110592,118098,122880,128000,
   138240,157464,192000,196830,207360,221184,295245,314928,320000,331776,
   384000,414720,472392,512000,531441,552960,590490,640000,663552,787320,
   944784,960000]

/-- The 102-element replacement set in the article. -/
def integerExchangeReplacement : Finset ℕ := replacementValues.toFinset

/-- The charge for insertions at the boundary of the smooth part. -/
noncomputable def integerExchangeCharge : ℝ := 824341 / 10^7

/-- The certified gain in reciprocal mass after the boundary charge. -/
noncomputable def integerExchangeGain : ℝ := 237 / 100000

/-- Reciprocal mass on a set of positive integers. -/
noncomputable def integerExchangeReciprocalWeight (A : Set ℕ) : ℝ :=
  ∑' a : A, (a.val:ℝ)⁻¹

theorem integerExchangeReplacement_card : integerExchangeReplacement.card = 102 := by
  rw [integerExchangeReplacement, List.toFinset_card_of_nodup (by decide)]
  decide

private theorem replacementValues_smooth :
    replacementValues.all (fun n ↦ decide (n ∈ Nat.smoothNumbers 6 ∧ n ≤ 1000000)) = true := by
  decide +kernel

theorem integerExchangeReplacement_smooth :
    ∀ n ∈ integerExchangeReplacement, n ∈ Nat.smoothNumbers 6 ∧ n ≤ 1000000 := by
  intro n hn
  have hl : n ∈ replacementValues := List.mem_toFinset.mp hn
  exact of_decide_eq_true (List.all_eq_true.mp replacementValues_smooth n hl)

private def checkIntegralProgressions (xs : List ℕ) : Bool :=
  xs.all fun a ↦ xs.all fun b ↦
    if a < b ∧ a ∣ b then !xs.contains (b*b/a) else true

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem replacementValues_checked : checkIntegralProgressions replacementValues = true := by
  decide +kernel

private theorem checkedIntegral_admissible (xs : List ℕ)
    (hpos : ∀ n ∈ xs, 0 < n) (hcheck : checkIntegralProgressions xs = true) :
    IntegerPrefixAdmissible true (xs.toFinset : Set ℕ) := by
  intro a b c ha hb hc hab _ he hd
  have hA := List.mem_toFinset.mp ha
  have hB := List.mem_toFinset.mp hb
  have hC := List.mem_toFinset.mp hc
  have h := List.all_eq_true.mp (List.all_eq_true.mp hcheck a hA) b hB
  have hlast : b*b/a = c := by rw [← he, Nat.mul_div_cancel_left _ (hpos a hA)]
  rw [if_pos ⟨hab, hd rfl⟩, hlast, List.contains_iff_mem.mpr hC] at h
  exact Bool.noConfusion h

theorem integerExchangeReplacement_admissible :
    IntegerPrefixAdmissible true (integerExchangeReplacement : Set ℕ) :=
  checkedIntegral_admissible replacementValues (fun n hn ↦
    Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers
      (integerExchangeReplacement_smooth n (List.mem_toFinset.mpr hn)).1)) replacementValues_checked

theorem integerExchangeCharge_nonneg : 0 ≤ integerExchangeCharge := by
  norm_num [integerExchangeCharge]

theorem integerExchangeCharge_lt_one : integerExchangeCharge < 1 := by
  norm_num [integerExchangeCharge]

theorem integerExchangeGain_pos : 0 < integerExchangeGain := by
  norm_num [integerExchangeGain]

set_option maxRecDepth 30000 in
theorem integerExchangeReplacement_weight :
    integerExchangeReciprocalWeight (integerExchangeReplacement : Set ℕ) =
      (1928068463873:ℝ) / 680244480000 := by
  change (∑' a : ↥integerExchangeReplacement, (a.val:ℝ)⁻¹) = _
  rw [Finset.tsum_subtype integerExchangeReplacement (fun n : ℕ ↦ (n:ℝ)⁻¹)]
  have h : (∑ n ∈ integerExchangeReplacement, (n:ℚ)⁻¹) =
      (1928068463873:ℚ) / 680244480000 := by
    rw [integerExchangeReplacement, List.sum_toFinset _ (by decide)]
    decide +kernel
  have hc := congrArg (fun q : ℚ ↦ (q : ℝ)) h
  push_cast at hc
  exact hc

end GRHArticle.ProgressionFree
