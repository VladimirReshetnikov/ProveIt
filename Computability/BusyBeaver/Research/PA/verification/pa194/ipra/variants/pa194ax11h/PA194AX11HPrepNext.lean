import PA194AX11HPrepSource
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HPrepNext
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceRegisters PA194SourceInstructionModel PA194SourceControllerCode PA194AX11HPrepRows PA194AX11HSource
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- Each preparation instruction stays in its block or reaches the comparison exit. -/
theorem next_index (i : Fin 37) (s : M) :
    ∃ j : Fin 38, pi₁ (instructionSem (some (newPrep.getD i.val .halt)) s) =
      modelNumeral M (3605+j.val) := by
  fin_cases i
  · by_cases hz : getSem 4 (pi₂ s) = (0 : M)
    · refine ⟨⟨4,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
    · refine ⟨⟨1,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
  · refine ⟨⟨2,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · refine ⟨⟨3,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · refine ⟨⟨0,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · by_cases hz : getSem 6 (pi₂ s) = (0 : M)
    · refine ⟨⟨7,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
    · refine ⟨⟨5,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
  · refine ⟨⟨6,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · refine ⟨⟨4,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · by_cases hz : getSem 2 (pi₂ s) = (0 : M)
    · refine ⟨⟨15,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
    · refine ⟨⟨8,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
  · refine ⟨⟨9,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · by_cases hz : getSem 6 (pi₂ s) = (0 : M)
    · refine ⟨⟨11,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
    · refine ⟨⟨10,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
  · refine ⟨⟨14,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · by_cases hz : getSem 7 (pi₂ s) = (0 : M)
    · refine ⟨⟨14,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
    · refine ⟨⟨12,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
  · refine ⟨⟨13,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · refine ⟨⟨11,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · refine ⟨⟨7,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · by_cases hz : getSem 7 (pi₂ s) = (0 : M)
    · refine ⟨⟨18,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
    · refine ⟨⟨16,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
  · refine ⟨⟨17,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · refine ⟨⟨15,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · by_cases hz : getSem 1 (pi₂ s) = (0 : M)
    · refine ⟨⟨22,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
    · refine ⟨⟨19,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
  · refine ⟨⟨20,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · refine ⟨⟨21,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · refine ⟨⟨18,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · by_cases hz : getSem 6 (pi₂ s) = (0 : M)
    · refine ⟨⟨28,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
    · refine ⟨⟨23,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
  · refine ⟨⟨24,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · by_cases hz : getSem 6 (pi₂ s) = (0 : M)
    · refine ⟨⟨27,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
    · refine ⟨⟨25,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
  · refine ⟨⟨26,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · refine ⟨⟨24,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · refine ⟨⟨18,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · by_cases hz : getSem 7 (pi₂ s) = (0 : M)
    · refine ⟨⟨34,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
    · refine ⟨⟨29,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
  · refine ⟨⟨30,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · refine ⟨⟨31,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · refine ⟨⟨32,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · refine ⟨⟨33,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · refine ⟨⟨28,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · by_cases hz : getSem 1 (pi₂ s) = (0 : M)
    · refine ⟨⟨37,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
    · refine ⟨⟨35,by decide⟩,?_⟩
      simp [newPrep,instructionSem,destination,hz]
  · refine ⟨⟨36,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]
  · refine ⟨⟨34,by decide⟩,?_⟩
    simp [newPrep,instructionSem,destination]

#print axioms next_index
end models
end PA194AX11HPrepNext
