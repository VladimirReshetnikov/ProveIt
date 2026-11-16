import PA194RegisterBoxes
import PA194RegisterMark
import PA194SpareSweep
import PA194LCAX11HData
import PA194RegisterIncrement
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

namespace PA194LCAX11HBoxAgreement
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194CompressedBoxOracle PA194CompressedIncrementOracle PA194OneSpareReturn
open ConPA.Machine.Compressed
open PA194LCAX11HData (table denseControl)
open M6.Runtime (Branch sk)

/-- The exact dense literal rows used by the decrement routine. -/
def decrementRows : ConPA.Machine.GenericDecrement.Rows table where
  scanRight := 1
  testMarker := 3
  testValue := 4
  readFollowing := 5
  scanBack := 6
  returnPositive := 7
  clearMarker := 8
  returnZero := 11
  enterBlock := rfl
  scanRightOne := rfl
  enterMarked := rfl
  skipOrdinary := rfl
  readZero := rfl
  readPositive := rfl
  turnAfterZero := rfl
  finishPositiveBlock := rfl
  scanBackOne := rfl
  enterPositiveBlock := rfl
  restoreSeparator := rfl
  restoreOne := rfl
  scanZeroOne := rfl

/-- The exact dense rows used to locate a marked register before increment. -/
def incrementRows : ConPA.Machine.GenericIncrement.Rows table decrementRows where
  start := 2
  afterSeparator := 0
  enterBlock := rfl
  scanOnce := rfl
  skipOrdinary := rfl
  foundMark := rfl

/-- Appending a spare uses one more literal row from the dense table. -/
theorem spareRows : PA194SpareSweep.Rows table decrementRows where
  sealTail := rfl

def markRows : ConPA.Machine.GenericMark.Rows table where
  control p := denseControl (sk p)
  writeQ := 14
  firstReturn := 15
  backQ := 16
  returnQ := 17
  markEntry := rfl
  markWrite := rfl
  markBack := rfl
  skipRow := by intro p hp; interval_cases p <;> rfl
  skipLoop := by intro p hp; interval_cases p <;> rfl
  backFirst := rfl
  backLater := rfl
  backLoop := rfl
  backExit := rfl

theorem markExit (p : Fin 9) :
    ConPA.Machine.GenericMark.returnControl markRows p.val = denseControl (M6.Runtime.markExit p.val) := by
  fin_cases p <;> decide +kernel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- All literal AX11H register operations for the repeated-spare encoded file. -/
theorem concreteBoxAgreement (a : Fin 11 → M) (count : M) (br : Branch)
    (tail : a 10 = F repeatOutput ![count,(0 : M)]) (branch : BranchOK a br) :
    BoxAgreement table denseControl br (boxValue a (incremented a count)) := by
  refine PA194RegisterBoxes.boxAgreement table denseControl a (incremented a count) br branch ?_ ?_ ?_ ?_
  · intro p l
    have h := PA194RegisterMark.markOracle markRows p a l
    rw [markExit] at h
    exact h
  · intro p l
    rw [show denseControl 64 = 2 by decide +kernel, show denseControl 40 = 7 by decide +kernel]
    exact PA194RegisterIncrement.incrementOracle incrementRows
      spareRows p a count l tail
  · intro p l hz
    rw [show denseControl 0 = 1 by decide +kernel, show denseControl 97 = 11 by decide +kernel]
    exact PA194RegisterDecrement.zeroOracle decrementRows p a l hz
  · intro p l hp
    rw [show denseControl 0 = 1 by decide +kernel, show denseControl 40 = 7 by decide +kernel]
    exact PA194RegisterDecrement.positiveOracle decrementRows p a l hp

#print axioms markRows
#print axioms concreteBoxAgreement
end models
end PA194LCAX11HBoxAgreement
