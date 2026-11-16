import PA194AX11HPushSemantics
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HPushCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceInstructionModel PA194AX11HRelocation PA194AX11HPushRows PA194AX11HPushSemantics
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem sem_file_congr (i : Option M6.Source.Instruction) (s t : M) (h : pi₂ s = pi₂ t) :
    instructionSem i s = instructionSem i t := by
  cases i with
  | none => simp [instructionSem,h]
  | some i => cases i <;> simp [instructionSem,h]

/-- The old and revised source states may have different PCs; equality of
    their register files suffices for one relocated push instruction. -/
theorem pushInstruction_files (i : Fin 19) (s t : M) (h : pi₂ s = pi₂ t) :
    related (instructionSem (some (oldPush.getD i.val .halt)) s)
      (instructionSem (some (newPush.getD i.val .halt)) t) := by
  rw [← sem_file_congr _ s t h]
  exact pushInstruction i s

#print axioms sem_file_congr
#print axioms pushInstruction_files
end models
end PA194AX11HPushCongruence
