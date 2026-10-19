import BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240
import BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240
import BusyBeaver.ZFC.ArithmeticDecrementRotation240

set_option autoImplicit false

/-!
Concrete numeric endpoints for the four actual Rotation240 box macros.
The physical register positions are finite, but their values, the extra-spare
count and the complete left tape are arbitrary elements of an IΣ1 model.
The right exterior is blank. Increment adds exactly one value-one spare.
Positive decrement keeps the spare count and exposes its added left bit.

This adapter composes the literal checked Mark, Increment and Decrement
contracts with the pure 167+extra box interpretation. It assumes no box
runtime oracle and asserts no first exit, complete dispatch simulation or
internal PA consistency endpoint. Mira-Cult, Jeff Ketchersid, Andrew James
Wade and ProveIt retain the underlying machine/framework attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxEndpointsRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineUniformScansPerm252 ArithmeticMachineRunFromRotation240
open ArithmeticRegisterForwardPerm252 (registerBlock)
open ArithmeticRegisterCarryRotation240
open ArithmeticOneRegisterBlocksRotation240 ArithmeticCarryTraversalRotation240
open ArithmeticSymbolicBoxesRotation240
open SymbolicRotation240 (Reg Branch)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Mark exactly the selected physical header and return one cell left. -/
theorem box_mark_split (pre : List V) (value : V) (rest : List V) (r : Reg)
    (hr : pre.length = r.val) (extra left : V) :
    runFrom (2*fileClock pre+3)
      (frame (ArithmeticRegisterMarkRotation240.skipCode pre.length : V) left
        (boxPrefix (pre++value::rest) extra (.plain .unchanged) 0)) =
      leftFrame (ArithmeticRegisterMarkRotation240.markExitCode pre : V) left
        (boxPrefix (pre++value::rest) extra (.marked r) 0) := by
  simpa only [unchanged_split,marked_split pre value rest r hr] using
    ArithmeticRegisterMarkRotation240.mark_file pre (by rw [hr]; exact r.isLt)
      value left (fileTape rest (spareTail extra 0))

/-- The spare appended by increment is absorbed into the extra count. -/
theorem box_increment_split (pre : List V) (value : V) (rest : List V) (r : Reg)
    (hr : pre.length = r.val) (extra left : V) :
    runFrom (2*fileClock pre+2*value+2*fileClock rest+6*(167+extra)+11)
      (frame (seekState : V) left (boxPrefix (pre++value::rest) extra (.marked r) 0)) =
      leftFrame (returnZeroState : V) left
        (boxPrefix (pre++value::rest) extra (.plain (.increment r)) 0) := by
  simpa only [marked_split pre value rest r hr,increment_split pre value rest r hr,
    spareTail,add_assoc] using
    ArithmeticIncrementRotation240.increment_file pre rest value (167+extra) left

/-- The fixed permanent spares supply a following block when rest is empty. -/
theorem box_zero_split (pre rest : List V) (r : Reg)
    (hr : pre.length = r.val) (extra left : V) :
    runFrom (2*fileClock pre+7)
      (frame (carryState : V) left (boxPrefix (pre++(0 : V)::rest) extra (.marked r) 0)) =
      leftFrame (rollbackState : V) left
        (boxPrefix (pre++(0 : V)::rest) extra (.plain .unchanged) 0) := by
  rw [marked_split pre (0 : V) rest r hr,unchanged_split,bitPrefix_zero]
  cases rest with
  | nil =>
    simp only [fileTape]
    rw [spareTail_first]
    exact ArithmeticDecrementRotation240.zero_decrement_next pre (1 : V) left
      (oneBlocks (166+extra) 0)
  | cons next rest =>
    simp only [fileTape]
    exact ArithmeticDecrementRotation240.zero_decrement_next pre next left
      (fileTape rest (spareTail extra 0))

/-- The additional true cell is on the left tape, not hidden in the box. -/
theorem box_positive_split (pre rest : List V) (value : V) (r : Reg)
    (hr : pre.length = r.val) (extra left : V) :
    runFrom (2*fileClock pre+4)
      (frame (carryState : V) left
        (boxPrefix (pre++(value+1)::rest) extra (.marked r) 0)) =
      leftFrame (returnZeroState : V) (2*left+1)
        (boxPrefix (pre++(value+1)::rest) extra (.plain (.decrement r)) 0) := by
  simpa only [marked_split pre (value+1) rest r hr,
    decrement_positive_split pre value rest r hr] using
    ArithmeticDecrementRotation240.positive_decrement_boundary pre value left
      (fileTape rest (spareTail extra 0))

/-- The exact finite mark source/target states, with an internal clock. -/
theorem box_mark (br : Branch) (values : List V) (hv : ValidValues br values)
    (r : Reg) (extra left : V) :
    ∃ time : V, runFrom time
      (frame (ArithmeticMachinePerm252.stateCode (some (RegisterMarkRotation240.skip r.val)) : V)
        left (boxPrefix values extra (.plain .unchanged) 0)) =
      leftFrame (ArithmeticMachinePerm252.stateCode (some (SymbolicRotation240.markExit r)) : V)
        left (boxPrefix values extra (.marked r) 0) := by
  obtain ⟨pre,value,rest,he,hl,_⟩ := split_register r.val values (by
    have := r.isLt; have := hv.1; omega)
  have exit :
      (ArithmeticMachinePerm252.stateCode (some (SymbolicRotation240.markExit r)) : V) =
        (ArithmeticRegisterMarkRotation240.markExitCode pre : V) := by
    have h := ArithmeticRegisterMarkRotation240.markExit_state_code pre
    rw [hl] at h
    exact congrArg (fun n : Nat => (n : V)) h
  rw [he,exit]
  refine ⟨2*fileClock pre+3,?_⟩
  change runFrom (2*fileClock pre+3)
    (frame (ArithmeticRegisterMarkRotation240.skipCode r.val : V) left
      (boxPrefix (pre++value::rest) extra (.plain .unchanged) 0)) = _
  simpa only [hl] using box_mark_split pre value rest r hl extra left

/-- The exact increment source/target; only the selected value and extra count change. -/
theorem box_increment (br : Branch) (values : List V) (hv : ValidValues br values)
    (r : Reg) (extra left : V) :
    ∃ time : V, runFrom time
      (frame (ArithmeticMachinePerm252.stateCode (some Rotation240Boxes.seek) : V) left
        (boxPrefix values extra (.marked r) 0)) =
      leftFrame (ArithmeticMachinePerm252.stateCode (some Rotation240Boxes.returnZero) : V) left
        (boxPrefix values extra (.plain (.increment r)) 0) := by
  obtain ⟨pre,value,rest,he,hl,_⟩ := split_register r.val values (by
    have := r.isLt; have := hv.1; omega)
  rw [he]
  exact ⟨2*fileClock pre+2*value+2*fileClock rest+6*(167+extra)+11,
    box_increment_split pre value rest r hl extra left⟩

/-- A zero target is restored without an additional spare-count premise. -/
theorem box_zero_decrement (values : List V) (r : Reg)
    (hv : ValidValues (some (r,true)) values) (extra left : V) :
    ∃ time : V, runFrom time
      (frame (ArithmeticMachinePerm252.stateCode (some Rotation240Boxes.carry) : V) left
        (boxPrefix values extra (.marked r) 0)) =
      leftFrame (ArithmeticMachinePerm252.stateCode (some Rotation240Boxes.rollback) : V) left
        (boxPrefix values extra (.plain .unchanged) 0) := by
  obtain ⟨pre,value,rest,he,hl,hvalue⟩ := split_register r.val values (by
    have := r.isLt; have := hv.1; omega)
  have hz : value = 0 := hvalue.symm.trans hv.2
  rw [hz] at he
  rw [he]
  exact ⟨2*fileClock pre+7,box_zero_split pre rest r hl extra left⟩

/-- Positive decrement preserves every spare and exposes the shifted boundary. -/
theorem box_positive_decrement (values : List V) (r : Reg)
    (hv : ValidValues (some (r,false)) values) (extra left : V) :
    ∃ time : V, runFrom time
      (frame (ArithmeticMachinePerm252.stateCode (some Rotation240Boxes.carry) : V) left
        (boxPrefix values extra (.marked r) 0)) =
      leftFrame (ArithmeticMachinePerm252.stateCode (some Rotation240Boxes.returnZero) : V)
        (2*left+1) (boxPrefix values extra (.plain (.decrement r)) 0) := by
  obtain ⟨pre,value,rest,he,hl,hvalue⟩ := split_register r.val values (by
    have := r.isLt; have := hv.1; omega)
  have hn : value ≠ 0 := by intro hz; exact hv.2 (hvalue.trans hz)
  rcases zero_or_succ value with hz | ⟨value,rfl⟩
  · exact False.elim (hn hz)
  · rw [he]
    exact ⟨2*fileClock pre+4,box_positive_split pre rest value r hl extra left⟩

end SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxEndpointsRotation240
