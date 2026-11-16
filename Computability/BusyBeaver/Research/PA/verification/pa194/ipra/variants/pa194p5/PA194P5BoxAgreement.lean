import PA194RegisterBoxes
import PA194RegisterMark
import PA194P5IncrementRows
import PA194P5Data
import PA194RegisterIncrement
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

namespace PA194P5BoxAgreement
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194CompressedBoxOracle PA194CompressedIncrementOracle PA194OneSpareReturn
open ConPA.Machine.Compressed
open PA194P5Data (table denseControl)
open M6.Runtime (Branch sk)

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

/-- All literal P5 register operations for the repeated-spare encoded file. -/
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
    exact PA194RegisterIncrement.incrementOracle PA194P5IncrementRows.increment
      PA194P5IncrementRows.spare p a count l tail
  · intro p l hz
    rw [show denseControl 0 = 1 by decide +kernel, show denseControl 97 = 11 by decide +kernel]
    exact PA194RegisterDecrement.zeroOracle PA194P5DecrementRows.rows p a l hz
  · intro p l hp
    rw [show denseControl 0 = 1 by decide +kernel, show denseControl 40 = 7 by decide +kernel]
    exact PA194RegisterDecrement.positiveOracle PA194P5DecrementRows.rows p a l hp

#print axioms markRows
#print axioms concreteBoxAgreement
end models
end PA194P5BoxAgreement
