import CompactCellSupport

/-! Support of all local cell digits, including selectors and dummy. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactCellDigitSupported
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open CompactCellCopyCode CompactCellDigit CompactCellSupport

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A forbidden selector row is the only way a nonzero selector could
    lie outside the concrete low-mask support. -/
theorem cellDigit_supported (a d k : V) (ha : a ≠ 1) (hk : k < 8807)
    (h : cellDigit a d k ≠ 0) :
    ∃ n : ℕ, k = (n : V) ∧ n ∈ CompactConcreteMask.support := by
  by_cases hs : k < 943
  · have he : a = k := by
      by_contra hn
      exact h (by simp [cellDigit, hs, hn])
    obtain ⟨n, rfl⟩ := eq_nat_of_lt_nat (n := 8807) hk
    have hn : n < 943 := by exact_mod_cast hs
    have hne : n ≠ 1 := by
      intro hn1
      apply ha
      rw [he, hn1]
      simp
    refine ⟨n, rfl, ?_⟩
    simp [CompactConcreteMask.support, hn, hne]
  · by_cases hd : k = 1063
    · refine ⟨1063, ?_, ?_⟩
      · simpa using hd
      · exact CompactConcreteMask.special_mem
    · have hc : copyCode k ≠ 0 := by
        intro hc
        exact h (by simp [cellDigit, hs, hd, hc])
      exact copyCode_supported k hk hc

#print axioms CompactCellDigitSupported.cellDigit_supported
end CompactCellDigitSupported
