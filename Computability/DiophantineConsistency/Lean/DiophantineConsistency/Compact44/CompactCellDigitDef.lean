import DiophantineConsistency.Compact44.CompactCellDigit

/-! Definability of the local cell digit as a function of its position. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactCellDigitDef
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
open CompactCellCopyCode CompactWordCellClient CompactCellDigit

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cellDigit_definable (a d : V) : 𝚺₁-Function₁ (cellDigit a d) := by
  letI : 𝚺₁-Function₁[V] copyCode := copyCode_definable
  letI : 𝚺₁-Function₁[V] payload := payload_definable
  have hR : 𝚺₁.Definable (fun v : Fin 2 → V =>
      (v 1 < 943 ∧ a = v 1 ∧ v 0 = 1) ∨
      (v 1 < 943 ∧ a ≠ v 1 ∧ v 0 = 0) ∨
      (¬ v 1 < 943 ∧ v 1 = 1063 ∧ v 0 = d) ∨
      (¬ v 1 < 943 ∧ v 1 ≠ 1063 ∧ copyCode (v 1) = 0 ∧ v 0 = 0) ∨
      (¬ v 1 < 943 ∧ v 1 ≠ 1063 ∧ copyCode (v 1) ≠ 0 ∧
        v 0 = fbit (payload a) (copyCode (v 1) - 1))) := by
    simp_rw [fbit_eq_div]
    definability
  apply hR.of_iff
  intro v
  unfold cellDigit
  by_cases h1 : v 1 < 943 <;> by_cases h2 : a = v 1 <;>
    by_cases h3 : v 1 = 1063 <;> by_cases h4 : copyCode (v 1) = 0 <;>
      simp [h1, h2, h3, h4] <;> norm_num

#print axioms CompactCellDigitDef.cellDigit_definable
end CompactCellDigitDef
