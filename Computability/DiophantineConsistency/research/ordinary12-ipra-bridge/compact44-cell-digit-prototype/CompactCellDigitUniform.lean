import CompactCellDigitDef

/-! Definability of the local cell digit as a function of its position. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactCellDigitUniform
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
open CompactCellCopyCode CompactWordCellClient CompactCellDigit

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

#print axioms CompactCellDigitUniform.cellDigit_uniform
end CompactCellDigitUniform
