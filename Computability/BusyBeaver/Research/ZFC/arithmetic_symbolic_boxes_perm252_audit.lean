import BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252

open SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineGraphPerm252 ArithmeticMachineRunFromPerm252
open ArithmeticMachineUniformScansPerm252 ArithmeticRegisterForwardPerm252
open ArithmeticRegisterFilePerm252 ArithmeticZeroRegisterBlocks254
open ArithmeticSymbolicBoxesPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.fileCode_append
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.markedPrefix_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.increment_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.decrement_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.boxPrefix_even
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.box_back
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.box_mark_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.box_increment_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.box_zero_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.box_positive_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.state_skip
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.state_mark_exit
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.state_positive_exit
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.box_mark
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.box_increment
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.box_zero_decrement
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252.box_positive_decrement

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (pre rest : List V) (suffix : V) :
    fileCode (pre++rest) suffix = fileCode pre (fileCode rest suffix) :=
  fileCode_append pre rest suffix
example (values : List V) (r : Nat) (value : V) :
    (writeAt values r value).length = values.length := writeAt_length values r value
example (values : List V) (count suffix : V) :
    boxPrefix values count (.plain .unchanged) suffix =
      fileCode (values++fixedSpares) (zeroBlocks count (2*suffix)) := by
  rw [fileCode_append]
  rfl
example (pre : List V) (value : V) (rest : List V) (r : SymbolicPerm252.Reg)
    (hr : pre.length = r.val) (count suffix : V) :
    boxPrefix (pre++value::rest) count (.marked r) suffix =
      fileCode pre (4*bitPrefix true value (fileCode (rest++fixedSpares) (zeroBlocks count (2*suffix)))) :=
  marked_split pre value rest r hr count suffix
example (pre : List V) (value : V) (rest : List V) (r : SymbolicPerm252.Reg)
    (hr : pre.length = r.val) (count suffix : V) :
    boxPrefix (pre++value::rest) count (.plain (.increment r)) suffix =
      fileCode pre (registerBlock (value+1) (fileCode (rest++fixedSpares) (zeroBlocks count (2*suffix)))) :=
  increment_split pre value rest r hr count suffix
example (pre : List V) (value : V) (rest : List V) (r : SymbolicPerm252.Reg)
    (hr : pre.length = r.val) (count suffix : V) :
    boxPrefix (pre++value::rest) count (.plain (.decrement r)) suffix =
      fileCode pre (registerBlock (value-1) (fileCode (rest++fixedSpares) (zeroBlocks (count+1) (2*suffix)))) :=
  decrement_split pre value rest r hr count suffix
example (values : List V) (hlen : values.length = 9) (count suffix : V) (x : SymbolicPerm252.Box) :
    ∃ half : V, boxPrefix values count x suffix = 2*half :=
  boxPrefix_even values hlen count x suffix
example (values : List V) (hlen : values.length = 9) (count state target left : V)
    (x : SymbolicPerm252.Box) (hrow : actionLookup state (digit false) = 4*target+1+digit false) :
    runFrom 1 (frame state left (boxPrefix values count x 0)) =
      leftFrame target left (boxPrefix values count x 0) :=
  box_back values hlen count state target left x hrow
example (values : List V) (hlen : values.length = 9) (count state left : V)
    (x : SymbolicPerm252.Box) (hrow : actionLookup state (digit false) = 4*(0 : V)+1+digit false) :
    runFrom 1 (frame state left (boxPrefix values count x 0)) =
      leftFrame 0 left (boxPrefix values count x 0) :=
  box_back values hlen count state 0 left x hrow
example (pre : List V) (value : V) (rest : List V) (r : SymbolicPerm252.Reg)
    (hr : pre.length = r.val) (count left : V) :
    runFrom (2*fileTime pre+3)
      (frame (ArithmeticRegisterMarkPerm252.skipCode r.val : V) left
        (boxPrefix (pre++value::rest) count (.plain .unchanged) 0)) =
      leftFrame (ArithmeticRegisterMarkPerm252.markExit pre) left
        (boxPrefix (pre++value::rest) count (.marked r) 0) :=
  box_mark_split pre value rest r hr count left
example (pre : List V) (value : V) (rest : List V) (r : SymbolicPerm252.Reg)
    (hr : pre.length = r.val) (count left : V) :
    runFrom (2*fileTime pre+2*value+2*fileTime (rest++fixedSpares)+4*count+7)
      (frame 72 left (boxPrefix (pre++value::rest) count (.marked r) 0)) =
      leftFrame 48 left (boxPrefix (pre++value::rest) count (.plain (.increment r)) 0) :=
  box_increment_split pre value rest r hr count left
example (pre rest : List V) (r : SymbolicPerm252.Reg) (hr : pre.length = r.val)
    (count left : V) :
    runFrom (2*fileTime pre+5)
      (frame 43 left (boxPrefix (pre++(0 : V)::rest) count (.marked r) 0)) =
      leftFrame 5 left (boxPrefix (pre++(0 : V)::rest) count (.plain .unchanged) 0) :=
  box_zero_split pre rest r hr count left
example (pre rest : List V) (value : V) (r : SymbolicPerm252.Reg)
    (hr : pre.length = r.val) (count left : V) :
    runFrom (2*fileTime pre+2*value+2*fileTime (rest++fixedSpares)+4*count+9)
      (frame 43 left (boxPrefix (pre++(value+1)::rest) count (.marked r) 0)) =
      leftFrame (ArithmeticRegisterDecrementPerm252.positiveExit pre) left
        (boxPrefix (pre++(value+1)::rest) count (.plain (.decrement r)) 0) :=
  box_positive_split pre rest value r hr count left
example (r : SymbolicPerm252.Reg) :
    stateValue (V := V) (some (RegisterMarkPerm252.skip r.val)) =
      (ArithmeticRegisterMarkPerm252.skipCode r.val : V) := state_skip r
example (pre : List V) (r : SymbolicPerm252.Reg) (hr : pre.length = r.val) :
    stateValue (some (SymbolicPerm252.markExit r)) = ArithmeticRegisterMarkPerm252.markExit pre :=
  state_mark_exit pre r hr
example (pre : List V) (r : SymbolicPerm252.Reg) (hr : pre.length = r.val) :
    stateValue (some (SymbolicPerm252.positiveExit r)) = ArithmeticRegisterDecrementPerm252.positiveExit pre :=
  state_positive_exit pre r hr
example (br : SymbolicPerm252.Branch) (values : List V) (hv : ValidValues br values)
    (r : SymbolicPerm252.Reg) (count left : V) :
    ∃ time : V, runFrom time
      (frame (stateValue (some (RegisterMarkPerm252.skip r.val))) left
        (boxPrefix values count (.plain .unchanged) 0)) =
      leftFrame (stateValue (some (SymbolicPerm252.markExit r))) left
        (boxPrefix values count (.marked r) 0) := box_mark br values hv r count left
example (br : SymbolicPerm252.Branch) (values : List V) (hv : ValidValues br values)
    (r : SymbolicPerm252.Reg) (count left : V) :
    ∃ time : V, runFrom time
      (frame (stateValue (some RegisterIncrementPerm252.seekInc)) left
        (boxPrefix values count (.marked r) 0)) =
      leftFrame (stateValue (some RegisterIncrementPerm252.incReturnZero)) left
        (boxPrefix values count (.plain (.increment r)) 0) := box_increment br values hv r count left
example (values : List V) (r : SymbolicPerm252.Reg)
    (hv : ValidValues (some (r,true)) values) (count left : V) :
    ∃ time : V, runFrom time
      (frame (stateValue (some RegisterBoxesPerm252.seekDec)) left
        (boxPrefix values count (.marked r) 0)) =
      leftFrame (stateValue (some RegisterBoxesPerm252.returnZero)) left
        (boxPrefix values count (.plain .unchanged) 0) := box_zero_decrement values r hv count left
example (values : List V) (r : SymbolicPerm252.Reg)
    (hv : ValidValues (some (r,false)) values) (count left : V) :
    ∃ time : V, runFrom time
      (frame (stateValue (some RegisterBoxesPerm252.seekDec)) left
        (boxPrefix values count (.marked r) 0)) =
      leftFrame (stateValue (some (SymbolicPerm252.positiveExit r))) left
        (boxPrefix values count (.plain (.decrement r)) 0) := box_positive_decrement values r hv count left
end
