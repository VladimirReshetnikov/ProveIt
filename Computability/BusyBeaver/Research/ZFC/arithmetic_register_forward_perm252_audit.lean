import BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252 ArithmeticRegisterForwardPerm252
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252.step_right_row
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252.right_transition_of_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252.step_right_numeral
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252.registerBlock_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252.reverseBlock_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252.registerBlock_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252.forward_block
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252.forward_dec
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252.forward_inc
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252.forward_suffix
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (read write : Bool) (q target left suffix : V) (hrow : actionLookup q (digit read) = 4*target+3+digit write) : stepValue (frame q left (2*suffix+digit read)) = frame target (2*left+digit write) suffix := step_right_row read write q target hrow left suffix
example (read write : Bool) (q target : Nat) (hrow : lookupNat literalRows 0 q read.toNat = 4*target+3+write.toNat) : actionLookup (q : V) (digit read) = 4*(target : V)+3+digit write := right_transition_of_nat read write q target hrow
example (left suffix : V) : stepValue (frame 76 left (2*suffix+1)) = frame 0 (2*left+1) suffix := by simpa [digit] using step_right_numeral true true 76 0 (by decide) left suffix
example (out value suffix : V) : registerBlockDef.val.Evalb ![out,value,suffix] ↔ out = registerBlock value suffix := by simp
example (out value left : V) : reverseBlockDef.val.Evalb ![out,value,left] ↔ out = reverseBlock value left := by simp
example (suffix : V) : registerBlock 0 suffix = 4*suffix+2 := registerBlock_zero suffix
example (seek probe value left suffix : V) (h0 : actionLookup seek (digit false) = 4*probe+3+digit false) (hp : actionLookup probe (digit true) = 4*seek+3+digit true) (h1 : actionLookup seek (digit true) = 4*seek+3+digit true) : runFrom (value+2) (frame seek left (registerBlock value suffix)) = frame seek (reverseBlock value left) suffix := forward_block seek probe h0 hp h1 value left suffix
example (value left suffix : V) : runFrom (value+2) (frame 43 left (registerBlock value suffix)) = frame 43 (reverseBlock value left) suffix := forward_dec value left suffix
example (value left suffix : V) : runFrom (value+2) (frame 72 left (registerBlock value suffix)) = frame 72 (reverseBlock value left) suffix := forward_inc value left suffix
example (value left suffix : V) : runFrom (value+2) (frame 84 left (registerBlock value suffix)) = frame 84 (reverseBlock value left) suffix := forward_suffix value left suffix
example (left suffix : V) : runFrom 2 (frame 72 left (4*suffix+2)) = frame 72 (reverseBlock 0 left) suffix := by simpa only [zero_add, registerBlock_zero] using forward_inc (0 : V) left suffix
example (value left suffix : V) : runFrom (value+2) (frame 72 left (registerBlock value (2*suffix+1))) = frame 72 (reverseBlock value left) (2*suffix+1) := forward_inc value left (2*suffix+1)
