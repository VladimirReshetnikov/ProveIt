import DiophantineConsistency.CurrentCellTranslation2011

/-!
# The coarse whole-field offset split

Actual sparse support and three known source ones reduce the field offset
to0,19,20. The two-selector contradiction uses one translated cell and the
proved actual physical selector count. No labels, occupation, or supplied
alignment are used; even a separate Booleanity assumption is unnecessary.
-/

namespace DiophantineConsistency.CurrentFieldOffsets2011

open CurrentCellTranslation2011 CurrentClause2011 CurrentMasks2011
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

/-- Two distinct unit entries force a natural finite sum to be at least two. -/
theorem two_ones_sum_ge_two {ι : Type*} [Fintype ι] (f : ι → ℕ) (i j : ι)
    (hij : i ≠ j) (hi : f i = 1) (hj : f j = 1) : 2 ≤ ∑ a, f a := by
  classical
  have hsum : (∑ a ∈ ({i, j} : Finset ι), f a) ≤ ∑ a, f a :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  simpa only [Finset.sum_pair hij, hi, hj] using hsum

theorem support_cases {e : ℕ} (he : e ∈ lowSupport) : e ≤ 985 ∨ e = 1004 := by
  simp only [lowSupport_def, Finset.mem_union, Finset.mem_range,
    Finset.mem_Ico, Finset.mem_singleton] at he
  omega

theorem support_le_1004 {e : ℕ} (he : e ∈ lowSupport) : e ≤ 1004 := by
  have h := support_cases he
  omega

variable {N : ℕ} [NeZero (N * 2011)]

omit [NeZero (N * 2011)] in
theorem source_support (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (t e : ℕ) (hone : c ((e : ZMod (N * 2011)) - (t : ZMod (N * 2011))) = 1) :
    ((e : ZMod (N * 2011)) - (t : ZMod (N * 2011))).val % 2011 ∈ lowSupport := by
  by_contra hnot
  have hz := hsupport _ hnot
  omega

/-- The shifted marker first bounds the remainder and excludes offsets1..18. -/
theorem marker_remainder_bounds (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (t : ℕ) (hmarker : c (1004 - (t : ZMod (N * 2011))) = 1) :
    t % 2011 ≤ 1004 ∧ (t % 2011 = 0 ∨ 19 ≤ t % 2011) := by
  have hs := source_support c hsupport t 1004 hmarker
  simp only [Nat.cast_ofNat] at hs
  have hmax := support_le_1004 hs
  have hr : t % 2011 < 2011 := Nat.mod_lt t (by decide)
  have hle : t % 2011 ≤ 1004 := by
    by_contra hnot
    have he := source_residue_of_lt_remainder (0 : Cell N) t 1004 (by omega)
    simp only [coe_zero, zero_add, Nat.cast_ofNat] at he
    omega
  have he := source_residue_of_remainder_le (0 : Cell N) t 1004 (by decide) hle
  simp only [coe_zero, zero_add, Nat.cast_ofNat] at he
  have hcases := support_cases hs
  exact ⟨hle, by omega⟩

/-- The forced source at961 cannot wrap above the supported fields once
the marker has supplied its bound. -/
theorem remainder_le_961 (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (t : ℕ) (hle : t % 2011 ≤ 1004)
    (h961 : c (961 - (t : ZMod (N * 2011))) = 1) : t % 2011 ≤ 961 := by
  have hs := source_support c hsupport t 961 h961
  simp only [Nat.cast_ofNat] at hs
  have hmax := support_le_1004 hs
  by_contra hnot
  have he := source_residue_of_lt_remainder (0 : Cell N) t 961 (by omega)
  simp only [coe_zero, zero_add, Nat.cast_ofNat] at he
  omega

omit [NeZero (N * 2011)] in
/-- The actual count includes every physical selector exactly once. -/
theorem two_distinct_selectors_force_count (c : ZMod (N * 2011) → ℕ)
    (b : ZMod (N * 2011)) (i j : Fin 942) (hij : i ≠ j)
    (hi : c (b + (i.val : ZMod (N * 2011))) = 1)
    (hj : c (b + (j.val : ZMod (N * 2011))) = 1) :
    2 ≤ selectorCount c b := by
  have hsum := two_ones_sum_ge_two
    (fun p : Fin 942 => c (b + (p.val : ZMod (N * 2011)))) i j hij hi hj
  have he : (∑ p : Fin 942, c (b + (p.val : ZMod (N * 2011)))) = selectorCount c b := by
    rw [selectorCount_eq_prefix, PaddingStaircase.prefixSum]
    exact Fin.sum_univ_eq_sum_range (fun p : ℕ => c (b + (p : ZMod (N * 2011)))) 942
  exact he ▸ hsum

/-- Offsets21..961 put the two given ones at distinct physical selector
positions in the same exact cell `theta t 0`, contrary to its count. -/
theorem not_middle_offset (c : ZMod (N * 2011) → ℕ) (t : ℕ)
    (hcount : ∀ b : Cell N, selectorCount c (b : ZMod (N * 2011)) ≤ 1)
    (h961 : c (961 - (t : ZMod (N * 2011))) = 1)
    (h962 : c (962 - (t : ZMod (N * 2011))) = 1) :
    ¬ (21 ≤ t % 2011 ∧ t % 2011 ≤ 961) := by
  rintro ⟨hlo, hhi⟩
  let i : Fin 942 := ⟨961 - t % 2011, by omega⟩
  let j : Fin 942 := ⟨962 - t % 2011, by omega⟩
  have hij : i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    dsimp only [i, j] at hv
    omega
  have he1 := source_eq_of_remainder_le (0 : Cell N) t 961 hhi
  have he2 := source_eq_of_remainder_le (0 : Cell N) t 962 (by omega)
  simp only [coe_zero, zero_add, Nat.cast_ofNat] at he1 he2
  have hi : c (((theta t (0 : Cell N) : Cell N) : ZMod (N * 2011)) +
      (i.val : ZMod (N * 2011))) = 1 := by
    change c (((theta t (0 : Cell N) : Cell N) : ZMod (N * 2011)) +
      ((961 - t % 2011 : ℕ) : ZMod (N * 2011))) = 1
    rw [← he1]
    exact h961
  have hj : c (((theta t (0 : Cell N) : Cell N) : ZMod (N * 2011)) +
      (j.val : ZMod (N * 2011))) = 1 := by
    change c (((theta t (0 : Cell N) : Cell N) : ZMod (N * 2011)) +
      ((962 - t % 2011 : ℕ) : ZMod (N * 2011))) = 1
    rw [← he2]
    exact h962
  have htwo := two_distinct_selectors_force_count c _ i j hij hi hj
  have hone := hcount (theta t 0)
  omega

/-- The complete coarse split from support, count and three source ones.
Their native derivation remains outside this arithmetic theorem. -/
theorem coarse_offset (c : ZMod (N * 2011) → ℕ) (t : ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hcount : ∀ b : Cell N, selectorCount c (b : ZMod (N * 2011)) ≤ 1)
    (hmarker : c (1004 - (t : ZMod (N * 2011))) = 1)
    (h961 : c (961 - (t : ZMod (N * 2011))) = 1)
    (h962 : c (962 - (t : ZMod (N * 2011))) = 1) :
    t % 2011 = 0 ∨ t % 2011 = 19 ∨ t % 2011 = 20 := by
  obtain ⟨hle, hgap⟩ := marker_remainder_bounds c hsupport t hmarker
  have hsmall := remainder_le_961 c hsupport t hle h961
  have hnot := not_middle_offset c t hcount h961 h962
  omega

end DiophantineConsistency.CurrentFieldOffsets2011
