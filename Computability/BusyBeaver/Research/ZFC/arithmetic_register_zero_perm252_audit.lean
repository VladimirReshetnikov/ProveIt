import BusyBeaver.ZFC.ArithmeticRegisterZeroPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252 ArithmeticZeroRegisterBlocks254
open ArithmeticZeroSpareScanPerm252 ArithmeticRegisterFilePerm252
open ArithmeticRegisterZeroPerm252
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterZeroPerm252.restore_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterZeroPerm252.return_dec_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterZeroPerm252.return_zero_prefix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterZeroPerm252.zero_box
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterZeroPerm252.file_zero_tail_even
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterZeroPerm252.zero_decrement
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (left right : V) :
    runFrom 4 (frame 43 left (8*right)) = frame 3 left (8*right+2) :=
  restore_zero left right
example (pre : List V) (left right : V) :
    runFrom (fileTime pre) (leftFrame 5 (reverseFile pre left) right) =
      leftFrame 5 left (fileCode pre right) := return_dec_file pre left right
example (pre : List V) (left right : V) :
    runFrom (fileTime pre+1) (frame 3 (reverseFile pre left) (2*right)) =
      leftFrame 5 left (fileCode pre (2*right)) := return_zero_prefix pre left right
example (pre : List V) (left right : V) :
    runFrom (2*fileTime pre+5) (frame 43 left (fileCode pre (8*right))) =
      leftFrame 5 left (fileCode pre (8*right+2)) := zero_box pre left right
example (rest : List V) (count : V) :
    ∃ half : V, fileCode rest (zeroBlocks count 0) = 2*half :=
  file_zero_tail_even rest count
example (pre rest : List V) (count left : V) :
    runFrom (2*fileTime pre+5)
        (frame 43 left (fileCode pre (4*fileCode rest (zeroBlocks count 0)))) =
      leftFrame 5 left
        (fileCode pre (registerBlock 0 (fileCode rest (zeroBlocks count 0)))) :=
  zero_decrement pre rest count left
example (count left : V) :
    runFrom 5 (frame 43 left (4*zeroBlocks count 0)) =
      leftFrame 5 left (registerBlock 0 (zeroBlocks count 0)) := by
  simpa [fileTime, fileCode] using zero_decrement ([] : List V) [] count left
example (pre rest : List V) (left : V) :
    runFrom (2*fileTime pre+5) (frame 43 left (fileCode pre (4*fileCode rest 0))) =
      leftFrame 5 left (fileCode pre (registerBlock 0 (fileCode rest 0))) := by
  simpa only [zeroBlocks_zero] using zero_decrement pre rest (0 : V) left
example (pre rest : List V) (count left : V) :
    runFrom (2*fileTime pre+5)
        (frame 43 left (fileCode pre (4*fileCode
          (rest ++ List.replicate 8 0 ++ [1]) (zeroBlocks (56+count) 0)))) =
      leftFrame 5 left (fileCode pre (registerBlock 0
        (fileCode (rest ++ List.replicate 8 0 ++ [1]) (zeroBlocks (56+count) 0)))) :=
  zero_decrement pre (rest ++ List.replicate 8 0 ++ [1]) (56+count) left
example (x y count left : V) :
    runFrom (2*fileTime [x]+5)
        (frame 43 left (fileCode [x] (4*fileCode [y,1] (zeroBlocks count 0)))) =
      leftFrame 5 left (fileCode [x]
        (registerBlock 0 (fileCode [y,1] (zeroBlocks count 0)))) :=
  zero_decrement [x] [y,1] count left
