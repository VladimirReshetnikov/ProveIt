import PA194LCAX11HData
import PA194AX11HSource
import PA194SourceContracts

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194LCAX11HChecks
open M6.Source
open PA194LCAX11HData

def programAt (i : Nat) : Option Instruction := (PA194AX11HSource.program[i]?).join

def validTarget (instruction : Instruction) : Bool :=
  let valid (target : Option Nat) := target.any (fun j => decide (j < 3671))
  match instruction with
  | .inc _ next | .jump next => valid next
  | .dec _ zero positive => valid zero && valid positive
  | .halt => true

abbrev checkInstruction := PA194SourceContracts.checkInstruction machine path

def checkAt (i : Nat) : Bool :=
  decide (programAt i = codeAt i) &&
    (programAt i).any (fun instruction => validTarget instruction && checkInstruction i instruction)

abbrev blockCheck := PA194SourceContracts.blockCheck checkAt

def AllContracts : Prop := ∀ i : Nat, i < 3671 → checkAt i = true

theorem block_sound {base count i : Nat} (h : blockCheck base count = true)
    (lo : base ≤ i) (hi : i < base + count) : checkAt i = true :=
  PA194SourceContracts.block_sound h lo hi

theorem checked_at (i : Nat) (h : checkAt i = true) :
    ∃ instruction, programAt i = some instruction ∧ codeAt i = some instruction ∧
      validTarget instruction = true ∧ checkInstruction i instruction = true := by
  cases found : programAt i with
  | none => simp [checkAt, found] at h
  | some instruction =>
    simp only [checkAt, found, Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨instruction, rfl, h.1.symm, h.2.1, h.2.2⟩

theorem representative :
    checkAt 10 = true ∧ checkAt 25 = true ∧ checkAt 3519 = true ∧
      checkAt 3553 = true ∧ checkAt 3572 = true ∧ checkAt 3605 = true ∧
      checkAt 3642 = true ∧ checkAt 3659 = true ∧ checkAt 3670 = true := by
  decide +kernel

#print axioms checked_at
#print axioms representative
end PA194LCAX11HChecks
