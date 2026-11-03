import CompactCellDigit
import DiophantineConsistency.CompactConcreteMask

/-! Nonzero compact copy digits only occur in the concrete low-mask support. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace CompactCellSupport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open CompactCellCopyCode CompactCellDigit

def naturalCode (n : ℕ) : ℕ :=
  if n = 1095 then 39 else if n = 2195 then 40 else if n = 3296 then 41
  else if 983 ≤ n then nearCodes.getD (n - 983) 0 else 0

/-- Finite lookup support, independent of the row and payload values. -/
theorem naturalCode_support (n : ℕ) (h : naturalCode n ≠ 0) :
    n ∈ CompactConcreteMask.support := by
  by_cases h1 : n = 1095
  · subst n; simp [CompactConcreteMask.support]
  by_cases h2 : n = 2195
  · subst n; simp [CompactConcreteMask.support]
  by_cases h3 : n = 3296
  · subst n; simp [CompactConcreteMask.support]
  by_cases h4 : 983 ≤ n
  · have hr : n < 1032 := by
      by_contra hn
      have hn' : nearCodes.length ≤ n - 983 := by simp [nearCodes]; omega
      have hz : nearCodes.getD (n - 983) 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hn']
        rfl
      simp [naturalCode, h1, h2, h3, h4, hz] at h
    interval_cases n <;> norm_num [naturalCode, nearCodes, CompactConcreteMask.support] at *
  · simp [naturalCode, h1, h2, h3, h4] at h

/-- Any nonzero model copy code below the cell width has supported position. -/
theorem copyCode_supported {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (k : V) (hk : k < 8807) (h : copyCode k ≠ 0) :
    ∃ n : ℕ, k = (n : V) ∧ n ∈ CompactConcreteMask.support := by
  obtain ⟨n, rfl⟩ := eq_nat_of_lt_nat (n := 8807) hk
  have hn : naturalCode n ≠ 0 := by
    intro hz
    rw [copyCode_cast] at h
    exact h (by simp [← naturalCode, hz])
  exact ⟨n, rfl, naturalCode_support n hn⟩

#print axioms CompactCellSupport.naturalCode_support
#print axioms CompactCellSupport.copyCode_supported
end CompactCellSupport
