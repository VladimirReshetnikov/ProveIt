import GRHArticle.ProgressionFree.IntegerRoughOptimalPrefix

/-!
# The jump set of the smooth prefix optimum

The maximum cardinal can increase by one only when a new smooth number
enters the prefix. The set of increasing cutoffs has exactly those maximum
prefix counts, whether or not one admissible set attains every cutoff.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped Classical BigOperators

/-- Any finite admissible smooth prefix has cardinal at most the optimum. -/
theorem card_le_integerSmoothPrefixMaximum {integral : Bool} {Y k : ℕ} {B : Finset ℕ}
    (hB : B ⊆ integerPrefixSlice (Nat.smoothNumbers (Y+1)) k)
    (hA : IntegerPrefixAdmissible integral (B : Set ℕ)) :
    B.card ≤ integerSmoothPrefixMaximum integral Y k := by
  unfold integerSmoothPrefixMaximum
  exact Finset.le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_powerset.mpr hB,hA⟩)

private theorem integerSmoothPrefixMaximum_mono (integral : Bool) (Y : ℕ) :
    Monotone (integerSmoothPrefixMaximum integral Y) := by
  intro k l hkl
  obtain ⟨B, hB, hA, hcard⟩ := exists_integerSmoothPrefixMaximum integral Y k
  rw [← hcard]
  refine card_le_integerSmoothPrefixMaximum (hB.trans ?_) hA
  intro n hn
  simp only [integerPrefixSlice, mem_filter, integerPrefix, mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans hkl⟩, hn.2⟩

private theorem integerSmoothPrefixMaximum_succ_le (integral : Bool) (Y k : ℕ) :
    integerSmoothPrefixMaximum integral Y (k+1) ≤ integerSmoothPrefixMaximum integral Y k +
      if k+1 ∈ Nat.smoothNumbers (Y+1) then 1 else 0 := by
  obtain ⟨B, hB, hA, hcard⟩ := exists_integerSmoothPrefixMaximum integral Y (k+1)
  let C := B.erase (k+1)
  have hC : C ⊆ integerPrefixSlice (Nat.smoothNumbers (Y+1)) k := by
    intro n hn
    obtain ⟨hne, hn⟩ := mem_erase.mp hn
    have hs := hB hn
    simp only [integerPrefixSlice, mem_filter, integerPrefix, mem_Icc] at hs ⊢
    exact ⟨⟨hs.1.1, by omega⟩, hs.2⟩
  have hAdm : IntegerPrefixAdmissible integral (C : Set ℕ) := by
    intro a b c ha hb hc
    exact hA (erase_subset _ _ ha) (erase_subset _ _ hb) (erase_subset _ _ hc)
  have hmax := card_le_integerSmoothPrefixMaximum hC hAdm
  by_cases h : k+1 ∈ B
  · have hs : k+1 ∈ Nat.smoothNumbers (Y+1) := by
      have hs := hB h
      simp only [integerPrefixSlice, mem_filter] at hs
      exact hs.2
    rw [if_pos hs, ← hcard, ← card_erase_add_one h]
    exact Nat.add_le_add_right hmax 1
  · have hc : C = B := erase_eq_of_notMem h
    rw [hc, hcard] at hmax
    exact hmax.trans (Nat.le_add_right ..)

private theorem integerSmoothPrefixMaximum_zero (integral : Bool) (Y : ℕ) :
    integerSmoothPrefixMaximum integral Y 0 = 0 := by
  obtain ⟨B, hB, _, hcard⟩ := exists_integerSmoothPrefixMaximum integral Y 0
  have hEmpty : integerPrefixSlice (Nat.smoothNumbers (Y+1)) 0 = ∅ := by
    ext n
    simp [integerPrefixSlice, integerPrefix]
  rw [hEmpty] at hB
  rw [← hcard, Finset.subset_empty.mp hB, Finset.card_empty]

/-- The positive cutoffs where the optimal smooth prefix cardinal increases. -/
def integerSmoothPrefixJumps (integral : Bool) (Y : ℕ) : Set ℕ :=
  {n | integerSmoothPrefixMaximum integral Y (n-1) < integerSmoothPrefixMaximum integral Y n}

theorem integerSmoothPrefixJumps_subset_smoothNumbers (integral : Bool) (Y : ℕ) :
    integerSmoothPrefixJumps integral Y ⊆ Nat.smoothNumbers (Y+1) := by
  intro n hn
  cases n with
  | zero =>
    change integerSmoothPrefixMaximum integral Y 0 < integerSmoothPrefixMaximum integral Y 0 at hn
    exact (lt_irrefl _ hn).elim
  | succ k =>
    have h := integerSmoothPrefixMaximum_succ_le integral Y k
    by_contra hs
    rw [if_neg hs, add_zero] at h
    exact (show integerSmoothPrefixMaximum integral Y k < integerSmoothPrefixMaximum integral Y (k+1) from hn).not_ge h

private theorem card_integerPrefixSlice_succ_local (A : Set ℕ) (k : ℕ) :
    (integerPrefixSlice A (k+1)).card = (integerPrefixSlice A k).card + if k+1 ∈ A then 1 else 0 := by
  have hI : integerPrefix (k+1) = insert (k+1) (integerPrefix k) := by
    ext n
    simp only [integerPrefix, mem_Icc, mem_insert]
    omega
  have hNot : k+1 ∉ integerPrefixSlice A k := fun h ↦ by
    have hk := (mem_Icc.mp (mem_filter.mp h).1).2
    omega
  simp only [integerPrefixSlice, hI, filter_insert]
  split_ifs with h
  · exact card_insert_of_notMem hNot
  · rw [Nat.add_zero]

/-- The jump set realizes the cardinality sequence of the separately chosen optimizers. -/
theorem card_integerPrefixSlice_smoothPrefixJumps (integral : Bool) (Y k : ℕ) :
    (integerPrefixSlice (integerSmoothPrefixJumps integral Y) k).card = integerSmoothPrefixMaximum integral Y k := by
  induction k with
  | zero =>
    rw [integerSmoothPrefixMaximum_zero]
    have hEmpty : integerPrefixSlice (integerSmoothPrefixJumps integral Y) 0 = ∅ := by
      ext n
      simp [integerPrefixSlice, integerPrefix]
    rw [hEmpty, Finset.card_empty]
  | succ k ih =>
    rw [card_integerPrefixSlice_succ_local, ih]
    have hlo : integerSmoothPrefixMaximum integral Y k ≤ integerSmoothPrefixMaximum integral Y (k+1) :=
      integerSmoothPrefixMaximum_mono integral Y (Nat.le_succ k)
    have hhi := integerSmoothPrefixMaximum_succ_le integral Y k
    have hhi' : integerSmoothPrefixMaximum integral Y (k+1) ≤ integerSmoothPrefixMaximum integral Y k + 1 := by
      by_cases h : k+1 ∈ Nat.smoothNumbers (Y+1)
      · simpa only [if_pos h] using hhi
      · simp only [if_neg h, Nat.add_zero] at hhi
        omega
    split_ifs with h
    · have ht : integerSmoothPrefixMaximum integral Y k < integerSmoothPrefixMaximum integral Y (k+1) := h
      omega
    · have ht : ¬ integerSmoothPrefixMaximum integral Y k < integerSmoothPrefixMaximum integral Y (k+1) := h
      omega

/-- The optimized weighted count is the reciprocal sum of the jump set times the rough density. -/
theorem integerSmoothUpperOptimization_eq_jump_reciprocal (integral : Bool) (Y : ℕ) :
    integerSmoothUpperOptimization integral Y = integerSmoothDensityFactor Y *
      ∑' n : integerSmoothPrefixJumps integral Y, (n.val : ℝ)⁻¹ := by
  let D := integerSmoothPrefixJumps integral Y
  have hsub : D ⊆ Nat.smoothNumbers (Y+1) := integerSmoothPrefixJumps_subset_smoothNumbers integral Y
  let emb : D → Nat.smoothNumbers (Y+1) := fun n ↦ ⟨n.val,hsub n.property⟩
  have hinj : Function.Injective emb := fun _ _ h ↦
    Subtype.ext (congrArg (fun n : Nat.smoothNumbers (Y+1) ↦ n.val) h)
  have hs : Summable (fun n : D ↦ (n.val : ℝ)⁻¹) := by
    simpa only [Function.comp_def, emb] using (summable_reciprocal_smoothNumbers Y).comp_injective hinj
  have hp : ∀ n ∈ D, 0 < n := fun n hn ↦ Nat.pos_of_ne_zero
    (Nat.ne_zero_of_mem_smoothNumbers (hsub hn))
  have h : HasSum (fun k ↦ (integerSmoothPrefixMaximum integral Y k : ℝ) * integerPrefixStepWeight k)
      (∑' n : D, (n.val : ℝ)⁻¹) := by
    apply (integerPrefix_hasSum_stepWeight D hp hs).congr_fun
    intro k
    rw [show (integerPrefixSlice D k).card = _ from card_integerPrefixSlice_smoothPrefixJumps integral Y k]
  exact congrArg (fun x : ℝ ↦ integerSmoothDensityFactor Y * x) h.tsum_eq

end GRHArticle.ProgressionFree
