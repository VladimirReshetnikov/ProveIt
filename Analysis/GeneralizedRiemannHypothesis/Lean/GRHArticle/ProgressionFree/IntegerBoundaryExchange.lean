import GRHArticle.ProgressionFree.IntegerBoundaryExchangeCertificate
import GRHArticle.ProgressionFree.IntegerBoundaryExchangeTail

/-!
# The finite 5-smooth exchange with its outside boundary charge
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators Classical

private noncomputable def reciprocal (n : ℕ) : ℝ := (n:ℝ)⁻¹

private theorem weight_indicator (A : Set ℕ) :
    integerExchangeReciprocalWeight A = ∑' n, A.indicator reciprocal n :=
  tsum_subtype A reciprocal

private theorem weight_summable {A : Set ℕ} (hA : A ⊆ Nat.smoothNumbers 6) :
    Summable (A.indicator reciprocal) := by
  have hs : Summable ((Nat.smoothNumbers 6).indicator reciprocal) :=
    summable_subtype_iff_indicator.mp (summable_reciprocal_smoothNumbers 5)
  apply hs.of_nonneg_of_le (fun _ ↦ Set.indicator_nonneg (fun n _ ↦ inv_nonneg.mpr (Nat.cast_nonneg n)) _)
  intro n
  by_cases h : n ∈ A
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hA h)]
    exact le_rfl
  · rw [Set.indicator_of_notMem h]
    exact Set.indicator_nonneg (s := Nat.smoothNumbers 6) (f := reciprocal)
      (fun n _ ↦ inv_nonneg.mpr (Nat.cast_nonneg n)) n

private theorem weight_mono {A D : Set ℕ} (h : A ⊆ D) (hD : D ⊆ Nat.smoothNumbers 6) :
    integerExchangeReciprocalWeight A ≤ integerExchangeReciprocalWeight D := by
  rw [weight_indicator, weight_indicator]
  apply (weight_summable (h.trans hD)).tsum_le_tsum _ (weight_summable hD)
  intro n
  by_cases hn : n ∈ A
  · rw [Set.indicator_of_mem hn, Set.indicator_of_mem (h hn)]
  · rw [Set.indicator_of_notMem hn]
    exact Set.indicator_nonneg (s := D) (f := reciprocal)
      (fun n _ ↦ inv_nonneg.mpr (Nat.cast_nonneg n)) n

private theorem weight_partition (A D : Set ℕ) (hA : A ⊆ Nat.smoothNumbers 6) :
    integerExchangeReciprocalWeight (A ∩ D) + integerExchangeReciprocalWeight (A \ D) =
      integerExchangeReciprocalWeight A := by
  simp only [weight_indicator]
  rw [← (weight_summable (fun _ h ↦ hA h.1)).tsum_add
    (weight_summable (fun _ h ↦ hA h.1))]
  apply tsum_congr
  intro n
  by_cases ha : n ∈ A <;> by_cases hd : n ∈ D <;> simp [ha, hd]

private theorem weight_finset (I : Finset ℕ) :
    integerExchangeReciprocalWeight (I : Set ℕ) = ∑ n ∈ I, (n:ℝ)⁻¹ := by
  change (∑' n : ↥I, (n.val:ℝ)⁻¹) = _
  exact I.tsum_subtype (fun n : ℕ ↦ (n:ℝ)⁻¹)

private theorem verticesSmooth {n : ℕ} (hn : n ∈ integerExchangeVertices) :
    n ∈ Nat.smoothNumbers 6 := (mem_integerExchangeVertices.mp hn).1

private theorem replacementSmooth {n : ℕ} (hn : n ∈ integerExchangeReplacement) :
    n ∈ Nat.smoothNumbers 6 := (integerExchangeReplacement_smooth n hn).1

private theorem weight_fiveSmooth :
    integerExchangeReciprocalWeight (Nat.smoothNumbers 6) = 15/4 := by
  have h := (hasSum_reciprocal_smoothNumbers 5).tsum_eq
  have hp : Nat.primesLE 5 = ({2,3,5} : Finset ℕ) := by decide
  change (∑' a : Nat.smoothNumbers 6, (a.val:ℝ)⁻¹) = 15/4
  rw [h, integerSmoothDensityFactor, hp]
  norm_num

private theorem weight_fiveSmooth_tail :
    integerExchangeReciprocalWeight (Nat.smoothNumbers 6 \ (integerExchangeVertices : Set ℕ)) =
      (12000753838363:ℝ)/108839116800000000 := by
  have hV : (integerExchangeVertices : Set ℕ) ⊆ Nat.smoothNumbers 6 :=
    fun n hn ↦ verticesSmooth hn
  have h := weight_partition (Nat.smoothNumbers 6) (integerExchangeVertices : Set ℕ) le_rfl
  rw [Set.inter_eq_right.mpr hV, weight_finset, integerExchangeVertices_reciprocal, weight_fiveSmooth] at h
  linarith only [h]

private theorem vertexWeighted_readback (I : Finset ℕ) :
    ∑ n ∈ I, integerExchangeVertexWeight n =
      integerExchangeReciprocalWeight (I : Set ℕ) -
        integerExchangeCharge * integerExchangeReciprocalWeight
          ((I.filter (· ∈ integerExchangeReplacement) : Finset ℕ) : Set ℕ) := by
  simp only [integerExchangeVertexWeight, sub_div, one_div, sum_sub_distrib, weight_finset]
  congr 1
  have h : (∑ n ∈ I, (if n ∈ integerExchangeReplacement then integerExchangeCharge else 0) / (n:ℝ)) =
      ∑ n ∈ I, if n ∈ integerExchangeReplacement then integerExchangeCharge * (n:ℝ)⁻¹ else 0 := by
    apply sum_congr rfl
    intro n hn
    split_ifs <;> simp [div_eq_mul_inv]
  rw [h, ← sum_filter, mul_sum]

private theorem scaledVertexThreshold_readback :
    (2827908305897851139120000:ℝ) / (integerExchangeScale:ℝ) =
      (1-integerExchangeCharge) * integerExchangeReciprocalWeight (integerExchangeReplacement : Set ℕ) -
        (12000753838363:ℝ)/108839116800000000 - integerExchangeGain := by
  have hq : (2827908305897851139120000:ℚ) / (integerExchangeScale:ℚ) =
      (1-824341/10^7) * ((1928068463873:ℚ)/680244480000) -
        (12000753838363:ℚ)/108839116800000000 - 237/100000 := by
    decide +kernel
  have hr := congrArg (fun q : ℚ ↦ (q : ℝ)) hq
  push_cast at hr
  calc
    _ = (1-integerExchangeCharge) * ((1928068463873:ℝ)/680244480000) -
        (12000753838363:ℝ)/108839116800000000 - integerExchangeGain := by
      simpa only [integerExchangeCharge, integerExchangeGain] using hr
    _ = _ := congrArg (fun w : ℝ ↦ (1-integerExchangeCharge) * w -
      (12000753838363:ℝ)/108839116800000000 - integerExchangeGain)
      integerExchangeReplacement_weight.symm

set_option maxRecDepth 12000 in
private theorem vertexWeighted_le_of_admissible {I : Finset ℕ} (hI : I ⊆ integerExchangeVertices)
    (hfree : IntegerPrefixAdmissible false (I : Set ℕ)) :
    (∑ n ∈ I, integerExchangeVertexWeight n) ≤
      (1-integerExchangeCharge) * integerExchangeReciprocalWeight (integerExchangeReplacement : Set ℕ) -
        (12000753838363:ℝ)/108839116800000000 - integerExchangeGain := by
  have h : ((∑ n ∈ I, integerExchangeCapacity n : ℕ) : ℝ) ≤
      2827908305897851139120000 := by
    exact Nat.cast_le.mpr (integerExchangeCapacity_le_of_rational_admissible hI hfree)
  have hscale : 0 < (integerExchangeScale:ℝ) :=
    Nat.cast_pos.mpr (by decide : 0 < integerExchangeScale)
  have h' := div_le_div_of_nonneg_right h hscale.le
  rw [Nat.cast_sum, sum_div] at h'
  have he : (∑ n ∈ I, (integerExchangeCapacity n : ℝ)/integerExchangeScale) =
      ∑ n ∈ I, integerExchangeVertexWeight n :=
    sum_congr rfl (fun n hn ↦ integerExchangeCapacity_readback (hI hn))
  rw [he] at h'
  exact h'.trans_eq scaledVertexThreshold_readback

set_option maxRecDepth 12000 in
/-- The article's replacement improves every rational-ratio admissible
5-smooth set by the stated mass, even after charging all new insertions. -/
theorem integerExchange_boundary_gain {A : Set ℕ} (hA : A ⊆ Nat.smoothNumbers 6)
    (hfree : IntegerPrefixAdmissible false A) :
    integerExchangeGain ≤ integerExchangeReciprocalWeight (integerExchangeReplacement : Set ℕ) -
      integerExchangeReciprocalWeight A -
      integerExchangeCharge * integerExchangeReciprocalWeight ((integerExchangeReplacement : Set ℕ) \ A) := by
  let V := integerExchangeVertices
  let B := integerExchangeReplacement
  let I := V.filter (· ∈ A)
  let J := I.filter (· ∈ B)
  have hI : I ⊆ V := filter_subset _ _
  have hIA : (I : Set ℕ) = A ∩ (V : Set ℕ) := by ext n; simp [I, and_comm]
  have hJ : (J : Set ℕ) = (B : Set ℕ) ∩ A := by
    ext n
    simp only [J, I, mem_coe, mem_filter, Set.mem_inter_iff]
    exact ⟨fun ⟨⟨_,hA⟩,hB⟩ ↦ ⟨hB,hA⟩,
      fun ⟨hb,ha⟩ ↦ ⟨⟨integerExchangeReplacement_subset_vertices hb, ha⟩,hb⟩⟩
  have hIFree : IntegerPrefixAdmissible false (I : Set ℕ) := by
    intro a b c ha hb hc
    exact hfree (mem_filter.mp ha).2 (mem_filter.mp hb).2 (mem_filter.mp hc).2
  have hfinite := vertexWeighted_le_of_admissible hI hIFree
  rw [vertexWeighted_readback I] at hfinite
  change integerExchangeReciprocalWeight (I : Set ℕ) -
    integerExchangeCharge * integerExchangeReciprocalWeight (J : Set ℕ) ≤ _ at hfinite
  have hAs := weight_partition A (V : Set ℕ) hA
  have hBs := weight_partition (B : Set ℕ) A (fun _ hn ↦ replacementSmooth hn)
  have htail_sub : A \ (V : Set ℕ) ⊆ Nat.smoothNumbers 6 \ (V : Set ℕ) :=
    fun _ h ↦ ⟨hA h.1,h.2⟩
  have htail : integerExchangeReciprocalWeight (A \ (V : Set ℕ)) ≤
      (12000753838363:ℝ)/108839116800000000 :=
    (weight_mono htail_sub (fun _ h ↦ h.1)).trans_eq weight_fiveSmooth_tail
  rw [← hIA] at hAs
  rw [← hJ] at hBs
  have hcharged := congrArg (fun w : ℝ ↦ integerExchangeCharge*w) hBs
  rw [mul_add] at hcharged
  linarith only [hAs, hcharged, hfinite, htail]

end GRHArticle.ProgressionFree
