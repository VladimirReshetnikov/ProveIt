import BusyBeaver.ZFC.ArithmeticRegisterFilePerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticMachineGraphPerm252 ArithmeticMachineRunFromPerm252
open ArithmeticMachineUniformScansPerm252 ArithmeticRegisterForwardPerm252
open ArithmeticZeroRegisterBlocks254 ArithmeticZeroSpareScanPerm252
open ArithmeticRegisterFilePerm252
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterFilePerm252.forward_inc_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterFilePerm252.return_inc_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterFilePerm252.shift_carry
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterFilePerm252.shift_file_zero_spares
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterFilePerm252.return_file_zero_spares
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterFilePerm252.increment_file_zero_spares
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterFilePerm252.increment_zip
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (pre : List V) (left right : V) :
    runFrom (fileTime pre) (frame 72 left (fileCode pre right)) =
      frame 72 (reverseFile pre left) right := forward_inc_file pre left right
example (pre : List V) (left right : V) :
    runFrom (fileTime pre) (leftFrame 48 (reverseFile pre left) right) =
      leftFrame 48 left (fileCode pre right) := return_inc_file pre left right
example (value next left : V) :
    bitPrefix true (next+1) (4*bitPrefix true value left+2) =
      reverseBlock next (bitPrefix true (value+1) left) := shift_carry value next left
example (rest : List V) (value count left : V) :
    runFrom (value+fileTime rest+2*count+2)
        (frame 94 left (bitPrefix true value (fileCode rest (zeroBlocks count 0)))) =
      leftFrame 63
        (reverseZeroBlocks count (reverseFile rest (bitPrefix true (value+1) left))) 0 :=
  shift_file_zero_spares rest value count left
example (rest : List V) (entry value count left right : V)
    (h : actionLookup entry (digit true) = 4*63+2) :
    runFrom (fileTime rest+value+2+2*count)
        (leftFrame entry
          (reverseZeroBlocks count (reverseFile rest (reverseBlock value left))) right) =
      leftFrame 48 left (registerBlock value (fileCode rest (zeroBlocks count right))) :=
  return_file_zero_spares rest entry value count left right h
example (rest : List V) (value count left : V) :
    runFrom (2*value+2*fileTime rest+4*count+7)
        (frame 72 left (4*bitPrefix true value (fileCode rest (zeroBlocks count 0)))) =
      leftFrame 48 left (registerBlock (value+1) (fileCode rest (zeroBlocks count 0))) :=
  increment_file_zero_spares rest value count left
example (value count left : V) :
    runFrom (2*value+4*count+7)
        (frame 72 left (4*bitPrefix true value (zeroBlocks count 0))) =
      leftFrame 48 left (registerBlock (value+1) (zeroBlocks count 0)) := by
  simpa [fileTime, fileCode] using increment_file_zero_spares [] value count left
example (value next count left : V) :
    runFrom (2*value+2*(next+2)+4*count+7)
        (frame 72 left (4*bitPrefix true value (registerBlock next (zeroBlocks count 0)))) =
      leftFrame 48 left (registerBlock (value+1) (registerBlock next (zeroBlocks count 0))) := by
  simpa [fileTime, fileCode] using increment_file_zero_spares [next] value count left
example (value a b c d e f g h count left : V) :
    runFrom (2*value+2*fileTime [a,b,c,d,e,f,g,h]+4*count+7)
        (frame 72 left (4*bitPrefix true value
          (fileCode [a,b,c,d,e,f,g,h] (zeroBlocks count 0)))) =
      leftFrame 48 left (registerBlock (value+1)
        (fileCode [a,b,c,d,e,f,g,h] (zeroBlocks count 0))) :=
  increment_file_zero_spares [a,b,c,d,e,f,g,h] value count left
example (following : List V) (value count left : V) :
    runFrom (2*value+2*fileTime (following ++ List.replicate 8 0 ++ [1])+4*(56+count)+7)
        (frame 72 left (4*bitPrefix true value
          (fileCode (following ++ List.replicate 8 0 ++ [1]) (zeroBlocks (56+count) 0)))) =
      leftFrame 48 left (registerBlock (value+1)
        (fileCode (following ++ List.replicate 8 0 ++ [1]) (zeroBlocks (56+count) 0))) :=
  increment_file_zero_spares (following ++ List.replicate 8 0 ++ [1]) value (56+count) left
example (rest : List V) (value left : V) :
    runFrom (2*value+2*fileTime rest+7)
        (frame 72 left (4*bitPrefix true value (fileCode rest 0))) =
      leftFrame 48 left (registerBlock (value+1) (fileCode rest 0)) := by
  simpa using increment_file_zero_spares rest value (0 : V) left
example (rest : List V) (count left : V) :
    runFrom (2*fileTime rest+4*count+7)
        (frame 72 left (4*fileCode rest (zeroBlocks count 0))) =
      leftFrame 48 left (registerBlock 1 (fileCode rest (zeroBlocks count 0))) := by
  simpa using increment_file_zero_spares rest (0 : V) count left
example (pre rest : List V) (value count left : V) :
    runFrom (2*fileTime pre+2*value+2*fileTime rest+4*count+7)
        (frame 72 left (fileCode pre
          (4*bitPrefix true value (fileCode rest (zeroBlocks count 0))))) =
      leftFrame 48 left (fileCode pre
        (registerBlock (value+1) (fileCode rest (zeroBlocks count 0)))) :=
  increment_zip pre rest value count left
example (pre following : List V) (value count left : V) :
    runFrom (2*fileTime pre+2*value+
        2*fileTime (following ++ List.replicate 8 0 ++ [1])+4*(56+count)+7)
        (frame 72 left (fileCode pre (4*bitPrefix true value
          (fileCode (following ++ List.replicate 8 0 ++ [1]) (zeroBlocks (56+count) 0))))) =
      leftFrame 48 left (fileCode pre (registerBlock (value+1)
        (fileCode (following ++ List.replicate 8 0 ++ [1]) (zeroBlocks (56+count) 0)))) :=
  increment_zip pre (following ++ List.replicate 8 0 ++ [1]) value (56+count) left
