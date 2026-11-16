import PA194SourceInstructionModel
import PA194FiniteControls
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HRelocation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceInstructionModel PA194SourceControllerCode PA194FiniteControls
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

def related (old new : M) : Prop := pi₂ old = pi₂ new ∧
  pi₁ new + modelNumeral M 15 = pi₁ old

theorem relocatedInc (r : Fin 9) (k : Nat) (s : M) :
    related (instructionSem (some (.inc r (some (k+15)))) s)
      (instructionSem (some (.inc r (some k))) s) := by
  simp [related,instructionSem,destination,modelNumeralAdd]

theorem relocatedDec (r : Fin 9) (z p : Nat) (s : M) :
    related (instructionSem (some (.dec r (some (z+15)) (some (p+15)))) s)
      (instructionSem (some (.dec r (some z) (some p))) s) := by
  simp only [instructionSem]
  split <;> simp [related,destination,modelNumeralAdd]

theorem relocatedJump (k : Nat) (s : M) :
    related (instructionSem (some (.jump (some (k+15)))) s)
      (instructionSem (some (.jump (some k))) s) := by
  simp [related,instructionSem,destination,modelNumeralAdd]

#print axioms relocatedInc
#print axioms relocatedDec
#print axioms relocatedJump
end models
end PA194AX11HRelocation
