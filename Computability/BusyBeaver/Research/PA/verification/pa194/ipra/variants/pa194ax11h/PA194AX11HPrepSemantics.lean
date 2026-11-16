import PA194AX11HPrepRows
import PA194AX11HFieldSemantics
import PA194AX11HPushCongruence
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HPrepSemantics
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceInstructionModel PA194SourceControllerCode PA194FiniteControls
open PA194AX11HPrepRows PA194AX11HFieldSemantics PA194AX11HPushCongruence
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- Each comparison-preparation instruction is relocated by 18. -/
theorem prepInstruction (i : Fin 37) (s : M) :
    related (instructionSem (some (oldPrep.getD i.val .halt)) s)
      (instructionSem (some (newPrep.getD i.val .halt)) s) := by
  fin_cases i
  · exact relocatedDec 4 3591 3588 s
  · exact relocatedInc 1 3589 s
  · exact relocatedInc 6 3590 s
  · exact relocatedJump 3587 s
  · exact relocatedDec 6 3594 3592 s
  · exact relocatedInc 4 3593 s
  · exact relocatedJump 3591 s
  · exact relocatedDec 2 3602 3595 s
  · exact relocatedInc 7 3596 s
  · exact relocatedDec 6 3598 3597 s
  · exact relocatedJump 3601 s
  · exact relocatedDec 7 3601 3599 s
  · exact relocatedInc 6 3600 s
  · exact relocatedJump 3598 s
  · exact relocatedJump 3594 s
  · exact relocatedDec 7 3605 3603 s
  · exact relocatedInc 2 3604 s
  · exact relocatedJump 3602 s
  · exact relocatedDec 1 3609 3606 s
  · exact relocatedInc 7 3607 s
  · exact relocatedInc 6 3608 s
  · exact relocatedJump 3605 s
  · exact relocatedDec 6 3615 3610 s
  · exact relocatedInc 7 3611 s
  · exact relocatedDec 6 3614 3612 s
  · exact relocatedInc 1 3613 s
  · exact relocatedJump 3611 s
  · exact relocatedJump 3605 s
  · exact relocatedDec 7 3621 3616 s
  · exact relocatedInc 1 3617 s
  · exact relocatedInc 1 3618 s
  · exact relocatedInc 1 3619 s
  · exact relocatedInc 1 3620 s
  · exact relocatedJump 3615 s
  · exact relocatedDec 1 3624 3622 s
  · exact relocatedInc 6 3623 s
  · exact relocatedJump 3621 s

theorem prepInstruction_files (i : Fin 37) (s t : M) (hf : pi₂ s = pi₂ t) :
    related (instructionSem (some (oldPrep.getD i.val .halt)) s)
      (instructionSem (some (newPrep.getD i.val .halt)) t) := by
  rw [← sem_file_congr _ s t hf]
  exact prepInstruction i s

#print axioms prepInstruction
#print axioms prepInstruction_files
end models
end PA194AX11HPrepSemantics
