import BusyBeaver.ZFC.ArithmeticRegisterMarkPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticMachineGraphPerm252 ArithmeticMachineRunFromPerm252
open ArithmeticMachineUniformScansPerm252 ArithmeticRegisterForwardPerm252
open ArithmeticZeroRegisterBlocks254 ArithmeticRegisterFilePerm252
open ArithmeticRegisterMarkPerm252
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkPerm252.skip_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkPerm252.skip_next
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkPerm252.skip_block
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkPerm252.skip_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkPerm252.mark_steps
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkPerm252.return_mark_target
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkPerm252.return_mark_prefix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkPerm252.mark_file
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (j : Nat) (hj : j < 9) :
    actionLookup (skipCode j : V) (digit true) = 4*(skipCode j : V)+3+digit true := skip_one j hj
example (j : Nat) (hj : j < 8) :
    actionLookup (skipCode (j+1) : V) (digit false) =
      4*(skipCode j : V)+3+digit false := skip_next j hj
example (j : Nat) (hj : j < 8) (value left right : V) :
    runFrom (value+2) (frame (skipCode (j+1) : V) left (registerBlock value right)) =
      frame (skipCode j : V) (reverseBlock value left) right := skip_block j hj value left right
example (pre : List V) (hp : pre.length < 9) (left right : V) :
    runFrom (fileTime pre) (frame (skipCode pre.length : V) left (fileCode pre right)) =
      frame 60 (reverseFile pre left) right := skip_file pre hp left right
example (value left right : V) :
    runFrom 3 (frame 60 left (registerBlock value right)) =
      leftFrame 4 left (4*bitPrefix true value right) := mark_steps value left right
example (rest : List V) (entry value left right : V)
    (hentry : actionLookup entry (digit true) = 4*6+2) :
    runFrom (fileTime rest+value+2)
        (leftFrame entry (reverseFile rest (reverseBlock value left)) right) =
      leftFrame 7 left (registerBlock value (fileCode rest right)) :=
  return_mark_target rest entry value left right hentry
example (pre : List V) (left right : V) :
    runFrom (fileTime pre) (leftFrame 4 (reverseFile pre left) right) =
      leftFrame (markExit pre) left (fileCode pre right) := return_mark_prefix pre left right
example (pre : List V) (hp : pre.length < 9) (value left right : V) :
    runFrom (2*fileTime pre+3)
        (frame (skipCode pre.length : V) left (fileCode pre (registerBlock value right))) =
      leftFrame (markExit pre) left (fileCode pre (4*bitPrefix true value right)) :=
  mark_file pre hp value left right
example (left right : V) : runFrom 3 (frame 60 left (registerBlock 0 right)) =
    leftFrame 4 left (4*right) := by simpa using mark_steps (0 : V) left right
example (x value left right : V) :
    runFrom (2*fileTime [x]+3) (frame 44 left (fileCode [x] (registerBlock value right))) =
      leftFrame 7 left (fileCode [x] (4*bitPrefix true value right)) := by
  simpa only [List.length_cons, List.length_nil, skipCode, Nat.cast_ofNat, markExit] using
    mark_file [x] (by simp) value left right
example (pre rest : List V) (hp : pre.length < 9) (value count left : V) :
    runFrom (2*fileTime pre+3) (frame (skipCode pre.length : V) left
        (fileCode pre (registerBlock value
          (fileCode (rest ++ List.replicate 8 0 ++ [1]) (zeroBlocks (56+count) 0))))) =
      leftFrame (markExit pre) left (fileCode pre (4*bitPrefix true value
        (fileCode (rest ++ List.replicate 8 0 ++ [1]) (zeroBlocks (56+count) 0)))) :=
  mark_file pre hp value left _
example (x value left right : V) :
    runFrom (2*fileTime (List.replicate 8 x)+3)
        (frame 68 left (fileCode (List.replicate 8 x) (registerBlock value right))) =
      leftFrame 7 left (fileCode (List.replicate 8 x) (4*bitPrefix true value right)) := by
  simpa only [List.replicate, skipCode, List.length_cons, List.length_nil,
    Nat.cast_ofNat, markExit] using
    mark_file (List.replicate 8 x) (by simp) value left right
