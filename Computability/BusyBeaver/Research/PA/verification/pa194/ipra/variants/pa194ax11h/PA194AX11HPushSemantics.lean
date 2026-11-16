import PA194AX11HPushRows
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HPushSemantics
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceInstructionModel PA194AX11HRelocation PA194AX11HPushRows
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- Every one of the 19 source instructions preserves the same register file
    under the exact offset-15 relocation of both branch destinations. -/
theorem pushInstruction (i : Fin 19) (s : M) :
    related (instructionSem (some (oldPush.getD i.val .halt)) s)
      (instructionSem (some (newPush.getD i.val .halt)) s) := by
  fin_cases i
  · exact relocatedDec 1 3556 3554 s
  · exact relocatedInc 6 3555 s
  · exact relocatedJump 3553 s
  · exact relocatedDec 2 3559 3557 s
  · exact relocatedInc 1 3558 s
  · exact relocatedJump 3556 s
  · exact relocatedDec 1 3563 3560 s
  · exact relocatedInc 7 3561 s
  · exact relocatedInc 6 3562 s
  · exact relocatedJump 3559 s
  · exact relocatedDec 6 3569 3564 s
  · exact relocatedInc 7 3565 s
  · exact relocatedDec 6 3568 3566 s
  · exact relocatedInc 1 3567 s
  · exact relocatedJump 3565 s
  · exact relocatedJump 3559 s
  · exact relocatedDec 7 3572 3570 s
  · exact relocatedInc 2 3571 s
  · exact relocatedJump 3569 s

#print axioms pushInstruction
end models
end PA194AX11HPushSemantics
