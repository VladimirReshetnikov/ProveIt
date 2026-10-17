import BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticMachineStepPerm252 ArithmeticMachineRunFromPerm252
open ArithmeticMachineUniformScansPerm252 ArithmeticRegisterForwardPerm252
open ArithmeticRegisterReturnPerm252
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252.step_left_row
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252.step_left_recenter
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252.left_transition_of_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252.step_left_numeral
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252.return_block
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252.return_dec
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252.return_dec_probe
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252.return_mark
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252.return_mark_probe
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252.return_inc
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252.return_inc_probe
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (left suffix : V) : stepValue (frame 2 left (2*suffix)) = leftFrame 3 left (2*suffix+1) := by
  simpa [digit] using step_left_numeral false true 2 3 (by decide) left suffix
example (left suffix : V) : stepValue (frame 2 left (2*suffix+1)) = leftFrame 4 left (2*suffix) := by
  simpa [digit] using step_left_numeral true false 2 4 (by decide) left suffix
example (v left right : V) : runFrom (v+2) (leftFrame 3 (reverseBlock v left) right) = leftFrame 5 left (registerBlock v right) := return_dec v left right
example (v left right : V) : runFrom (v+2) (leftFrame 5 (reverseBlock v left) right) = leftFrame 5 left (registerBlock v right) := return_dec_probe v left right
example (v left right : V) : runFrom (v+2) (leftFrame 4 (reverseBlock v left) right) = leftFrame 7 left (registerBlock v right) := return_mark v left right
example (v left right : V) : runFrom (v+2) (leftFrame 7 (reverseBlock v left) right) = leftFrame 7 left (registerBlock v right) := return_mark_probe v left right
example (v left right : V) : runFrom (v+2) (leftFrame 63 (reverseBlock v left) right) = leftFrame 48 left (registerBlock v right) := return_inc v left right
example (v left right : V) : runFrom (v+2) (leftFrame 48 (reverseBlock v left) right) = leftFrame 48 left (registerBlock v right) := return_inc_probe v left right
example (left right : V) : runFrom 2 (leftFrame 48 (4*left+1) right) = leftFrame 48 left (4*right+2) := by
  have hr : reverseBlock (0 : V) left = 4*left+1 := by
    unfold reverseBlock
    rw [bitPrefix_succ, bitPrefix_zero]
    simp only [digit, if_true]
    ring
  simpa only [zero_add, hr, registerBlock_zero] using return_inc_probe (0 : V) left right
example (v right : V) : runFrom (v+2) (leftFrame 63 (reverseBlock v 0) right) = leftFrame 48 0 (registerBlock v right) := return_inc v 0 right
example (v left right : V) : runFrom (v+2) (leftFrame 48 (reverseBlock v (2*left+1)) (2*right+1)) = leftFrame 48 (2*left+1) (registerBlock v (2*right+1)) := return_inc_probe v (2*left+1) (2*right+1)
example (left right : V) : runFrom 2 (leftFrame 5 (reverseBlock 0 left) right) = leftFrame 5 left (registerBlock 0 right) := by simpa using return_dec_probe (0 : V) left right
