import GRHArticle.ProgressionFree.IntervalRothByteBound

/-!
# Reading exact Roth information from a mask certificate

Full initial masks bound the Roth number. Deleting zero tests whether
all largest sets contain zero; adding a bonus bit tests whether any
largest set can contain that position.
-/

namespace GRHArticle.ProgressionFree

open Finset

theorem rothNumberNat_le_of_byteCheck {n M : ℕ}
    (hc : intervalByteCheck M n (2^n-1) 0 = true) : rothNumberNat n ≤ M := by
  obtain ⟨B,hB,he,hf⟩ := rothNumberNat_spec n
  have h := intervalByteCheck_sound hc hf hB (fun j hj ↦ by simp [mem_range.mp (hB hj)])
  simpa [he] using h

theorem zero_mem_interval_of_byteCheck {n M : ℕ} (hM : 0<M)
    (hc : intervalByteCheck (M-1) n ((2^n-1) ^^^ 1) 0 = true)
    {B : Finset ℕ} (hB : B ⊆ range n) (hf : ThreeAPFree (B : Set ℕ))
    (hb : M ≤ B.card) : 0 ∈ B := by
  by_contra hz
  have h := intervalByteCheck_sound hc hf hB (by
    intro j hj
    have hj₀ : j ≠ 0 := fun he ↦ hz (he ▸ hj)
    have hb : Nat.testBit 1 j = false := by
      cases h : Nat.testBit 1 j with
      | false => rfl
      | true => exact (hj₀ (Nat.testBit_one_eq_true_iff_self_eq_zero.mp h)).elim
    simp [Nat.testBit_xor,mem_range.mp (hB hj),hb])
  simp at h
  omega

theorem notMem_interval_of_byteCheck {n M i : ℕ}
    (hc : intervalByteCheck M n (2^n-1) (2^i) = true)
    {B : Finset ℕ} (hB : B ⊆ range n) (hf : ThreeAPFree (B : Set ℕ))
    (hb : M ≤ B.card) : i ∉ B := by
  intro hi
  have h := intervalByteCheck_sound hc hf hB (fun j hj ↦ by simp [mem_range.mp (hB hj)])
  have hsum : (∑ j ∈ B, ((2^i : ℕ).testBit j).toNat) = 1 := by
    calc
      _ = ∑ j ∈ B, if j=i then 1 else 0 := by
        apply sum_congr rfl
        intro j _
        by_cases he : j=i <;> simp [he, Ne.symm]
      _ = _ := by simp [hi]
  rw [sum_add_distrib,hsum] at h
  simp at h
  omega

end GRHArticle.ProgressionFree
