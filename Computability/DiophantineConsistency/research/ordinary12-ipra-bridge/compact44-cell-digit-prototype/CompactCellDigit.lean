import CompactCellCopyCode

/-! A local digit function for a row and a dummy bit. This does not yet
construct a packed cell or prove mask and carry obligations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactCellDigit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open DiophantineConsistency.ArithmeticWindowDigits
open CompactSymbolicKernel CompactForwardCellInputs CompactWordCellClient CompactCellCopyCode

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The selector, dummy and copy cases are separated by their positions. -/
def cellDigit (a d k : V) : V :=
  if k < 943 then (if a = k then 1 else 0)
  else if k = 1063 then d
  else if copyCode k = 0 then 0
  else fbit (payload a) (copyCode k - 1)

theorem selector_digit (a d : V) (i : Fin 943) :
    cellDigit a d (i.val : V) = selector a i := by
  have hi : (i.val : V) < 943 := by exact_mod_cast i.isLt
  simp [cellDigit, selector, hi]

theorem dummy_digit (a d : V) : cellDigit a d 1063 = d := by
  simp [cellDigit, show ¬ (1063 : V) < 943 by norm_num]

theorem copy_digit (a d : V) (i : Fin 41) :
    cellDigit a d (position i : V) = payloadBit (payload a) i := by
  have hn : 943 ≤ position i := by fin_cases i <;> decide
  have hd : position i ≠ 1063 := by fin_cases i <;> decide
  have hnv : (943 : V) ≤ (position i : V) := by exact_mod_cast hn
  have hdv : (position i : V) ≠ 1063 := by exact_mod_cast hd
  have hc := at_slot (V := V) i
  have hz : ((i.val + 1 : ℕ) : V) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero i.val)
  have hs : ((i.val + 1 : ℕ) : V) - 1 = (i.val : V) := by simp
  simp only [cellDigit, not_lt.mpr hnv, hdv, if_false, hc, hz, hs, payloadBit]

theorem cellDigit_le_one (a d k : V) (hd : d ≤ 1) : cellDigit a d k ≤ 1 := by
  unfold cellDigit
  split
  · split <;> simp
  · split
    · exact hd
    · split
      · exact Arithmetic.zero_le _
      · exact fbit_le_one _ _

#print axioms CompactCellDigit.selector_digit
#print axioms CompactCellDigit.dummy_digit
#print axioms CompactCellDigit.copy_digit
#print axioms CompactCellDigit.cellDigit_le_one
end CompactCellDigit
