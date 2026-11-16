import PA194M6Data
import PA194M6Program
import PA194SourceContracts

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194M6Checks
open M6.Source
open PA194M6Data

abbrev programAt := PA194ProgramDrain.row PA194M6Program.program
abbrev checkInstruction := PA194SourceContracts.checkInstructionFor 3795 machine path

def checkAt (i : Nat) : Bool :=
  decide (programAt i = codeAt i) &&
    (programAt i).any (fun instruction =>
      decide (instruction = .halt ↔ i = 10) && checkInstruction i instruction)

abbrev blockCheck := PA194SourceContracts.blockCheck checkAt

def AllContracts : Prop := ∀ i : Nat, i < 3795 → checkAt i = true

theorem block_sound {base count i : Nat} (h : blockCheck base count = true)
    (lo : base ≤ i) (hi : i < base + count) : checkAt i = true :=
  PA194SourceContracts.block_sound h lo hi

theorem checked_at (i : Nat) (h : checkAt i = true) :
    ∃ instruction, programAt i = some instruction ∧ codeAt i = some instruction ∧
      (instruction = .halt ↔ i = 10) ∧ checkInstruction i instruction = true := by
  cases found : programAt i with
  | none => simp [checkAt, found] at h
  | some instruction =>
    simp only [checkAt, found, Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨instruction, rfl, h.1.symm, h.2.1, h.2.2⟩

theorem representative :
    checkAt 10 = true ∧ checkAt 25 = true ∧ checkAt 123 = true ∧
      checkAt 124 = true ∧ checkAt 128 = true ∧ checkAt 129 = true ∧
      checkAt 130 = true ∧ checkAt 131 = true ∧ checkAt 3674 = true ∧ checkAt 3794 = true := by
  decide +kernel

#print axioms checked_at
#print axioms representative
end PA194M6Checks
