import PA194AX11HFieldSource
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HFieldNext
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceRegisters PA194SourceInstructionModel PA194SourceControllerCode PA194AX11HFieldRows PA194AX11HSource
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- Every field instruction stays in its 14-site block or reaches its unique exit. -/
theorem next_index (i : Fin 14) (s : M) :
    ∃ j : Fin 15, pi₁ (instructionSem (some (newField.getD i.val .halt)) s) =
      modelNumeral M (3572+j.val) := by
  fin_cases i
  · by_cases hz : getSem 8 (pi₂ s) = (0 : M)
    · refine ⟨⟨8,by decide⟩,?_⟩
      simp [newField,instructionSem,destination,hz]
    · refine ⟨⟨1,by decide⟩,?_⟩
      simp [newField,instructionSem,destination,hz]
  · refine ⟨⟨2,by decide⟩,?_⟩
    simp [newField,instructionSem,destination]
  · by_cases hz : getSem 6 (pi₂ s) = (0 : M)
    · refine ⟨⟨4,by decide⟩,?_⟩
      simp [newField,instructionSem,destination,hz]
    · refine ⟨⟨3,by decide⟩,?_⟩
      simp [newField,instructionSem,destination,hz]
  · refine ⟨⟨7,by decide⟩,?_⟩
    simp [newField,instructionSem,destination]
  · by_cases hz : getSem 7 (pi₂ s) = (0 : M)
    · refine ⟨⟨7,by decide⟩,?_⟩
      simp [newField,instructionSem,destination,hz]
    · refine ⟨⟨5,by decide⟩,?_⟩
      simp [newField,instructionSem,destination,hz]
  · refine ⟨⟨6,by decide⟩,?_⟩
    simp [newField,instructionSem,destination]
  · refine ⟨⟨4,by decide⟩,?_⟩
    simp [newField,instructionSem,destination]
  · refine ⟨⟨0,by decide⟩,?_⟩
    simp [newField,instructionSem,destination]
  · by_cases hz : getSem 7 (pi₂ s) = (0 : M)
    · refine ⟨⟨11,by decide⟩,?_⟩
      simp [newField,instructionSem,destination,hz]
    · refine ⟨⟨9,by decide⟩,?_⟩
      simp [newField,instructionSem,destination,hz]
  · refine ⟨⟨10,by decide⟩,?_⟩
    simp [newField,instructionSem,destination]
  · refine ⟨⟨8,by decide⟩,?_⟩
    simp [newField,instructionSem,destination]
  · by_cases hz : getSem 6 (pi₂ s) = (0 : M)
    · refine ⟨⟨14,by decide⟩,?_⟩
      simp [newField,instructionSem,destination,hz]
    · refine ⟨⟨12,by decide⟩,?_⟩
      simp [newField,instructionSem,destination,hz]
  · refine ⟨⟨13,by decide⟩,?_⟩
    simp [newField,instructionSem,destination]
  · refine ⟨⟨11,by decide⟩,?_⟩
    simp [newField,instructionSem,destination]

#print axioms next_index
end models
end PA194AX11HFieldNext
