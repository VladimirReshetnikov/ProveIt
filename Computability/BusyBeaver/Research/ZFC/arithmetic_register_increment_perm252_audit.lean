import BusyBeaver.ZFC.ArithmeticRegisterIncrementPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252 ArithmeticRegisterReturnPerm252
open ArithmeticZeroRegisterBlocks254 ArithmeticZeroSpareScanPerm252
open ArithmeticRegisterIncrementPerm252
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterIncrementPerm252.restore_mark
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterIncrementPerm252.return_zero_spares
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterIncrementPerm252.return_zero_spares_inc_entry
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterIncrementPerm252.shifted_target_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterIncrementPerm252.increment_last_zero_spares
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (left suffix : V) : runFrom 2 (frame 72 left (4*suffix)) =
    frame 94 (4*left+1) suffix := restore_mark left suffix
example (entry value count left right : V)
    (h : ArithmeticMachineGraphPerm252.actionLookup entry (digit true) = 4*63+2) :
    runFrom (value+2+2*count)
        (leftFrame entry (reverseZeroBlocks count (reverseBlock value left)) right) =
      leftFrame 48 left (registerBlock value (zeroBlocks count right)) :=
  return_zero_spares entry value count left right h
example (value count left right : V) :
    runFrom (value+2+2*count)
        (leftFrame 63 (reverseZeroBlocks count (reverseBlock value left)) right) =
      leftFrame 48 left (registerBlock value (zeroBlocks count right)) :=
  return_zero_spares_inc_entry value count left right
example (value left : V) : bitPrefix true (value+1) (4*left+1) =
    reverseBlock (value+1) left := shifted_target_left value left
example (value count left : V) :
    runFrom (2*value+4*count+7)
        (frame 72 left (4*bitPrefix true value (zeroBlocks count 0))) =
      leftFrame 48 left (registerBlock (value+1) (zeroBlocks count 0)) :=
  increment_last_zero_spares value count left
example (value left : V) : runFrom (2*value+7) (frame 72 left (4*bitPrefix true value 0)) =
    leftFrame 48 left (registerBlock (value+1) 0) := by
  simpa using increment_last_zero_spares value (0 : V) left
example (count left : V) : runFrom (4*count+7) (frame 72 left (4*zeroBlocks count 0)) =
    leftFrame 48 left (registerBlock 1 (zeroBlocks count 0)) := by
  simpa using increment_last_zero_spares (0 : V) count left
example (value count left : V) :
    runFrom (2*value+4*(56+count)+7)
        (frame 72 left (4*bitPrefix true value (zeroBlocks (56+count) 0))) =
      leftFrame 48 left (registerBlock (value+1) (zeroBlocks (56+count) 0)) :=
  increment_last_zero_spares value (56+count) left
