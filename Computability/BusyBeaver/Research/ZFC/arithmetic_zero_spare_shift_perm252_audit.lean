import BusyBeaver.ZFC.ArithmeticZeroSpareShiftPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
open ArithmeticZeroRegisterBlocks254 ArithmeticZeroSpareScanPerm252
open ArithmeticZeroSpareShiftPerm252
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareShiftPerm252.shift_separator
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareShiftPerm252.shift_end
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareShiftPerm252.shift_zero_spares
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (left suffix : V) : runFrom 2 (frame 94 left (4*suffix+2)) = frame 94 (4*left+2) suffix := shift_separator left suffix
example (left : V) : runFrom 2 (frame 94 left 0) = leftFrame 63 (2*left+1) 0 := shift_end left
example (value count left : V) :
    runFrom (value+2*count+2) (frame 94 left (bitPrefix true value (zeroBlocks count 0))) =
      leftFrame 63 (reverseZeroBlocks count (bitPrefix true (value+1) left)) 0 :=
  shift_zero_spares value count left
example (value left : V) : runFrom (value+2) (frame 94 left (bitPrefix true value 0)) =
    leftFrame 63 (bitPrefix true (value+1) left) 0 := by
  simpa using shift_zero_spares value (0 : V) left
example (count left : V) : runFrom (2*count+2) (frame 94 left (zeroBlocks count 0)) =
    leftFrame 63 (reverseZeroBlocks count (2*left+1)) 0 := by
  have h : bitPrefix true (1 : V) left = 2*left+1 := by
    simpa only [zero_add, bitPrefix_zero, digit, if_true] using bitPrefix_succ true (0 : V) left
  simpa only [zero_add, bitPrefix_zero, h] using shift_zero_spares (0 : V) count left
example (value count left : V) :
    runFrom (value+2*(56+count)+2) (frame 94 left (bitPrefix true value (zeroBlocks (56+count) 0))) =
      leftFrame 63 (reverseZeroBlocks (56+count) (bitPrefix true (value+1) left)) 0 :=
  shift_zero_spares value (56+count) left
