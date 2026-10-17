import BusyBeaver.ZFC.ArithmeticRegisterDecrementPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252 ArithmeticZeroRegisterBlocks254
open ArithmeticZeroSpareScanPerm252 ArithmeticRegisterFilePerm252
open ArithmeticRegisterDecrementPerm252
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterDecrementPerm252.shift_block
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterDecrementPerm252.shift_zero_spares
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterDecrementPerm252.weave_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterDecrementPerm252.shift_file_zero_spares
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterDecrementPerm252.prepare_shift
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterDecrementPerm252.finish_shift
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterDecrementPerm252.prepare_positive
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterDecrementPerm252.positive_tail
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterDecrementPerm252.return_positive_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterDecrementPerm252.positive_decrement
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (value left right : V) :
    runFrom (value+2) (frame 111 (reverseBlock value left) (2*right)) =
      frame 111 left (2*bitPrefix true value (4*right+2)) := shift_block value left right
example (count left right : V) :
    runFrom (2*count) (frame 111 (reverseZeroBlocks count left) (2*right)) =
      frame 111 left (2*zeroBlocks count right) := shift_zero_spares count left right
example (rest : List V) (right : V) :
    4*weaveFile rest right+2 = fileCode rest (4*right+2) := weave_file rest right
example (rest : List V) (count left right : V) :
    runFrom (fileTime rest+2*count)
        (frame 111 (reverseZeroBlocks count (reverseFile rest left)) (2*right)) =
      frame 111 left (2*weaveFile rest (zeroBlocks count right)) :=
  shift_file_zero_spares rest count left right
example (left : V) : runFrom 2 (frame 84 left 0) = frame 111 left 0 := prepare_shift left
example (left right : V) :
    runFrom 2 (frame 111 (2*left) (2*right)) = leftFrame 63 left (4*right+2) :=
  finish_shift left right
example (value left right : V) :
    runFrom 3 (frame 43 left (4*bitPrefix true (value+1) right)) =
      frame 84 (8*left+1) (bitPrefix true value right) := prepare_positive value left right
example (rest : List V) (value count left : V) :
    runFrom (2*value+2*fileTime rest+4*count+9)
        (frame 43 left (4*bitPrefix true (value+1) (fileCode rest (zeroBlocks count 0)))) =
      leftFrame 63 left (registerBlock value (fileCode rest (zeroBlocks (count+1) 0))) :=
  positive_tail rest value count left
example (pre : List V) (left right : V) :
    runFrom (fileTime pre) (leftFrame 63 (reverseFile pre left) right) =
      leftFrame (positiveExit pre) left (fileCode pre right) := return_positive_file pre left right
example (pre rest : List V) (value count left : V) :
    runFrom (2*fileTime pre+2*value+2*fileTime rest+4*count+9)
        (frame 43 left (fileCode pre
          (4*bitPrefix true (value+1) (fileCode rest (zeroBlocks count 0))))) =
      leftFrame (positiveExit pre) left (fileCode pre
        (registerBlock value (fileCode rest (zeroBlocks (count+1) 0)))) :=
  positive_decrement pre rest value count left
example (value count left : V) :
    runFrom (2*value+4*count+9)
        (frame 43 left (4*bitPrefix true (value+1) (zeroBlocks count 0))) =
      leftFrame 63 left (registerBlock value (zeroBlocks (count+1) 0)) := by
  simpa [fileTime, fileCode, positiveExit] using
    positive_decrement ([] : List V) [] value count left
example (x y value count left : V) :
    runFrom (2*fileTime [x]+2*value+2*fileTime [y,1]+4*(56+count)+9)
        (frame 43 left (fileCode [x]
          (4*bitPrefix true (value+1) (fileCode [y,1] (zeroBlocks (56+count) 0))))) =
      leftFrame 48 left (fileCode [x]
        (registerBlock value (fileCode [y,1] (zeroBlocks ((56+count)+1) 0)))) := by
  simpa only [positiveExit] using
    positive_decrement [x] [y,1] value (56+count) left
