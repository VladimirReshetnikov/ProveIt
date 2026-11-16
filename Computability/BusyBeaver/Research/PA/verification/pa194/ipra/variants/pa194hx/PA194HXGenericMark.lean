import ConPAMachineGenericMark
import PA194HXDispatch
import PA194ORRegisterFile
import Mathlib.Tactic.IntervalCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194HXGenericMark
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ConPA.Machine ConPA.Machine.Compressed

/-- Dense HX controls corresponding to the native physical skip chain. -/
def control (n : Nat) : Nat := [113,93,68,114,95,71,85,60,97].getD n 113

def rows : ConPA.Machine.GenericMark.Rows PA194HXDispatch.table where
  control := control
  writeQ := 14
  firstReturn := 15
  backQ := 16
  returnQ := 17
  markEntry := by rfl
  markWrite := by rfl
  markBack := by rfl
  skipRow := by intro n hn; interval_cases n <;> rfl
  skipLoop := by intro n hn; interval_cases n <;> rfl
  backFirst := by rfl
  backLater := by rfl
  backLoop := by rfl
  backExit := by rfl

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Full physical mark path, using every HX row in the generic certificate. -/
theorem mark (previous : List V) (bound : previous.length < 9) (n l r : V) :
    Reach1 PA194HXDispatch.table
      (scanFrame true (control previous.length) l
        (PA194ORMark.file previous (PA194ORMark.block n r)))
      (scanFrame false (if previous.length = 0 then 15 else 17)
        (PA194ORMark.file previous (PA194ORMark.marked n r)) l) := by
  change Reach1 PA194HXDispatch.table
      (scanFrame true (rows.control previous.length) l
        (ConPA.Machine.GenericMark.file previous (ConPA.Machine.GenericMark.block n r)))
      (scanFrame false (ConPA.Machine.GenericMark.returnControl rows previous.length)
        (ConPA.Machine.GenericMark.file previous (ConPA.Machine.GenericMark.marked n r)) l)
  exact ConPA.Machine.GenericMark.mark rows previous bound n l r

#print axioms rows
#print axioms mark
end models
end PA194HXGenericMark
