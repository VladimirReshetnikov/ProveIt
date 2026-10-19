import BusyBeaver.ZFC.ArithmeticSymbolicBoxEndpointsRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachineUniformScansPerm252 ArithmeticMachineRunFromRotation240
open ArithmeticRegisterCarryRotation240 ArithmeticCarryTraversalRotation240
open ArithmeticSymbolicBoxesRotation240 ArithmeticSymbolicBoxEndpointsRotation240
open SymbolicRotation240 (Reg Branch)

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxEndpointsRotation240.box_mark_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxEndpointsRotation240.box_increment_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxEndpointsRotation240.box_zero_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxEndpointsRotation240.box_positive_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxEndpointsRotation240.box_mark
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxEndpointsRotation240.box_increment
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxEndpointsRotation240.box_zero_decrement
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxEndpointsRotation240.box_positive_decrement

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (pre rest : List V) (value : V) (r : Reg) (hr : pre.length = r.val) (extra left : V) :
    runFrom (2*fileClock pre+3)
      (frame (ArithmeticRegisterMarkRotation240.skipCode pre.length : V) left
        (boxPrefix (pre++value::rest) extra (.plain .unchanged) 0)) =
      leftFrame (ArithmeticRegisterMarkRotation240.markExitCode pre : V) left
        (boxPrefix (pre++value::rest) extra (.marked r) 0) :=
  box_mark_split pre value rest r hr extra left
example (pre rest : List V) (value : V) (r : Reg) (hr : pre.length = r.val) (extra left : V) :
    runFrom (2*fileClock pre+2*value+2*fileClock rest+6*(167+extra)+11)
      (frame (seekState : V) left (boxPrefix (pre++value::rest) extra (.marked r) 0)) =
      leftFrame (returnZeroState : V) left
        (boxPrefix (pre++value::rest) extra (.plain (.increment r)) 0) :=
  box_increment_split pre value rest r hr extra left
example (pre rest : List V) (r : Reg) (hr : pre.length = r.val) (extra left : V) :
    runFrom (2*fileClock pre+7)
      (frame (carryState : V) left (boxPrefix (pre++(0 : V)::rest) extra (.marked r) 0)) =
      leftFrame (rollbackState : V) left
        (boxPrefix (pre++(0 : V)::rest) extra (.plain .unchanged) 0) :=
  box_zero_split pre rest r hr extra left
example (pre rest : List V) (value : V) (r : Reg) (hr : pre.length = r.val) (extra left : V) :
    runFrom (2*fileClock pre+4)
      (frame (carryState : V) left (boxPrefix (pre++(value+1)::rest) extra (.marked r) 0)) =
      leftFrame (returnZeroState : V) (2*left+1)
        (boxPrefix (pre++(value+1)::rest) extra (.plain (.decrement r)) 0) :=
  box_positive_split pre rest value r hr extra left
example (br : Branch) (values : List V) (hv : ValidValues br values) (r : Reg) (extra left : V) :
    ∃ time : V, runFrom time
      (frame (ArithmeticMachinePerm252.stateCode (some (RegisterMarkRotation240.skip r.val)) : V)
        left (boxPrefix values extra (.plain .unchanged) 0)) =
      leftFrame (ArithmeticMachinePerm252.stateCode (some (SymbolicRotation240.markExit r)) : V)
        left (boxPrefix values extra (.marked r) 0) := box_mark br values hv r extra left
example (br : Branch) (values : List V) (hv : ValidValues br values) (r : Reg) (extra left : V) :
    ∃ time : V, runFrom time
      (frame (ArithmeticMachinePerm252.stateCode (some Rotation240Boxes.seek) : V) left
        (boxPrefix values extra (.marked r) 0)) =
      leftFrame (ArithmeticMachinePerm252.stateCode (some Rotation240Boxes.returnZero) : V) left
        (boxPrefix values extra (.plain (.increment r)) 0) := box_increment br values hv r extra left
example (values : List V) (r : Reg) (hv : ValidValues (some (r,true)) values) (extra left : V) :
    ∃ time : V, runFrom time
      (frame (ArithmeticMachinePerm252.stateCode (some Rotation240Boxes.carry) : V) left
        (boxPrefix values extra (.marked r) 0)) =
      leftFrame (ArithmeticMachinePerm252.stateCode (some Rotation240Boxes.rollback) : V) left
        (boxPrefix values extra (.plain .unchanged) 0) := box_zero_decrement values r hv extra left
example (values : List V) (r : Reg) (hv : ValidValues (some (r,false)) values) (extra left : V) :
    ∃ time : V, runFrom time
      (frame (ArithmeticMachinePerm252.stateCode (some Rotation240Boxes.carry) : V) left
        (boxPrefix values extra (.marked r) 0)) =
      leftFrame (ArithmeticMachinePerm252.stateCode (some Rotation240Boxes.returnZero) : V)
        (2*left+1) (boxPrefix values extra (.plain (.decrement r)) 0) :=
  box_positive_decrement values r hv extra left

-- The selected final physical slot is supported at zero extra spares too.
example (pre : List V) (hp : pre.length = 8) (left : V) :
    runFrom (2*fileClock pre+7)
      (frame (carryState : V) left (boxPrefix (pre++[0]) 0 (.marked ⟨8,by decide⟩) 0)) =
      leftFrame (rollbackState : V) left (boxPrefix (pre++[0]) 0 (.plain .unchanged) 0) :=
  box_zero_split pre [] ⟨8,by decide⟩ hp 0 left
-- The positive target exposes the added true cell rather than an extra spare.
example (pre rest : List V) (value : V) (r : Reg) (hr : pre.length = r.val) (extra left : V) :
    runFrom (2*fileClock pre+4)
      (frame (carryState : V) left (boxPrefix (pre++(value+1)::rest) extra (.marked r) 0)) =
      frame (returnZeroState : V) left
        (2*boxPrefix (pre++(value+1)::rest) extra (.plain (.decrement r)) 0+1) := by
  rw [box_positive_split pre rest value r hr,ArithmeticDecrementRotation240.leftFrame_one]
