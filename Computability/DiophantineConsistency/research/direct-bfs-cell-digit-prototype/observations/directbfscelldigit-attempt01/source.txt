import DirectBFSModelPayload
import CompactCellCopyCode

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSCellDigit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open DiophantineConsistency.ArithmeticWindowDigits
open CompactSymbolicKernel CompactForwardCellInputs DirectBFSModelPayload CompactCellCopyCode

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

#print axioms DirectBFSCellDigit.selector_digit
#print axioms DirectBFSCellDigit.dummy_digit
#print axioms DirectBFSCellDigit.copy_digit
#print axioms DirectBFSCellDigit.cellDigit_le_one
end DirectBFSCellDigit

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSCellDigitUniform
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
open CompactCellCopyCode DirectBFSModelPayload DirectBFSCellDigit

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cellDigit_uniform : 𝚺₁-Function₃ (cellDigit : V → V → V → V) := by
  letI : 𝚺₁-Function₁[V] copyCode := copyCode_definable
  letI : 𝚺₁-Function₁[V] payload := payload_definable
  have hR : 𝚺₁.Definable (fun v : Fin 4 → V =>
      (v 3 < 943 ∧ v 1 = v 3 ∧ v 0 = 1) ∨
      (v 3 < 943 ∧ v 1 ≠ v 3 ∧ v 0 = 0) ∨
      (¬ v 3 < 943 ∧ v 3 = 1063 ∧ v 0 = v 2) ∨
      (¬ v 3 < 943 ∧ v 3 ≠ 1063 ∧ copyCode (v 3) = 0 ∧ v 0 = 0) ∨
      (¬ v 3 < 943 ∧ v 3 ≠ 1063 ∧ copyCode (v 3) ≠ 0 ∧
        v 0 = fbit (payload (v 1)) (copyCode (v 3) - 1))) := by
    simp_rw [fbit_eq_div]
    definability
  apply hR.of_iff
  intro v
  unfold cellDigit
  by_cases h1 : v 3 < 943 <;> by_cases h2 : v 1 = v 3 <;>
    by_cases h3 : v 3 = 1063 <;> by_cases h4 : copyCode (v 3) = 0 <;>
      simp [h1, h2, h3, h4] <;> norm_num

#print axioms DirectBFSCellDigitUniform.cellDigit_uniform
end DirectBFSCellDigitUniform
