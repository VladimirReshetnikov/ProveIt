import PA194AX11HFieldRows
import PA194AX11HPushCongruence
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HFieldSemantics
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceInstructionModel PA194SourceControllerCode PA194FiniteControls
open PA194AX11HFieldRows PA194AX11HPushCongruence
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

def related (old new : M) : Prop := pi₂ old = pi₂ new ∧ pi₁ old + modelNumeral M 18 = pi₁ new

theorem relocatedInc (r : Fin 9) (k : Nat) (s : M) :
    related (instructionSem (some (.inc r (some k))) s)
      (instructionSem (some (.inc r (some (k+18)))) s) := by
  simp [related,instructionSem,destination,modelNumeralAdd]

theorem relocatedDec (r : Fin 9) (z p : Nat) (s : M) :
    related (instructionSem (some (.dec r (some z) (some p))) s)
      (instructionSem (some (.dec r (some (z+18)) (some (p+18)))) s) := by
  simp only [instructionSem]
  split <;> simp [related,destination,modelNumeralAdd]

theorem relocatedJump (k : Nat) (s : M) :
    related (instructionSem (some (.jump (some k))) s)
      (instructionSem (some (.jump (some (k+18)))) s) := by
  simp [related,instructionSem,destination,modelNumeralAdd]

theorem fieldInstruction (i : Fin 14) (s : M) :
    related (instructionSem (some (oldField.getD i.val .halt)) s)
      (instructionSem (some (newField.getD i.val .halt)) s) := by
  fin_cases i
  · exact relocatedDec 8 3562 3555 s
  · exact relocatedInc 7 3556 s
  · exact relocatedDec 6 3558 3557 s
  · exact relocatedJump 3561 s
  · exact relocatedDec 7 3561 3559 s
  · exact relocatedInc 6 3560 s
  · exact relocatedJump 3558 s
  · exact relocatedJump 3554 s
  · exact relocatedDec 7 3565 3563 s
  · exact relocatedInc 8 3564 s
  · exact relocatedJump 3562 s
  · exact relocatedDec 6 3568 3566 s
  · exact relocatedInc 4 3567 s
  · exact relocatedJump 3565 s

theorem fieldInstruction_files (i : Fin 14) (s t : M) (hf : pi₂ s = pi₂ t) :
    related (instructionSem (some (oldField.getD i.val .halt)) s)
      (instructionSem (some (newField.getD i.val .halt)) t) := by
  rw [← sem_file_congr _ s t hf]
  exact fieldInstruction i s

#print axioms fieldInstruction
#print axioms fieldInstruction_files
end models
end PA194AX11HFieldSemantics
