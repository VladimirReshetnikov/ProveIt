import PA194AX11HGateData
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HGateNext
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceRegisters PA194SourceInstructionModel PA194SourceControllerCode PA194AX11HGateData PA194AX11HSource
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- The 34-site gate has no outgoing edge other than its single exit. -/
theorem next_index (i : Fin 34) (s : M) :
    ∃ j : Fin 35, pi₁ (instructionSem (some (gateData.getD i.val .halt)) s) =
      modelNumeral M (3519+j.val) := by
  fin_cases i
  · by_cases hz : getSem 3 (pi₂ s) = (0 : M)
    · refine ⟨⟨4,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
    · refine ⟨⟨1,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
  · refine ⟨⟨2,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · refine ⟨⟨3,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · refine ⟨⟨0,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · by_cases hz : getSem 5 (pi₂ s) = (0 : M)
    · refine ⟨⟨8,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
    · refine ⟨⟨5,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
  · by_cases hz : getSem 6 (pi₂ s) = (0 : M)
    · refine ⟨⟨7,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
    · refine ⟨⟨6,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
  · refine ⟨⟨4,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · refine ⟨⟨9,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · by_cases hz : getSem 6 (pi₂ s) = (0 : M)
    · refine ⟨⟨14,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
    · refine ⟨⟨9,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
  · by_cases hz : getSem 5 (pi₂ s) = (0 : M)
    · refine ⟨⟨11,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
    · refine ⟨⟨10,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
  · refine ⟨⟨9,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · by_cases hz : getSem 6 (pi₂ s) = (0 : M)
    · refine ⟨⟨13,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
    · refine ⟨⟨12,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
  · refine ⟨⟨9,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · refine ⟨⟨16,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · by_cases hz : getSem 1 (pi₂ s) = (0 : M)
    · refine ⟨⟨16,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
    · refine ⟨⟨15,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
  · refine ⟨⟨14,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · by_cases hz : getSem 7 (pi₂ s) = (0 : M)
    · refine ⟨⟨19,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
    · refine ⟨⟨17,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
  · refine ⟨⟨18,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · refine ⟨⟨16,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · by_cases hz : getSem 4 (pi₂ s) = (0 : M)
    · refine ⟨⟨22,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
    · refine ⟨⟨20,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
  · refine ⟨⟨21,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · refine ⟨⟨19,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · by_cases hz : getSem 5 (pi₂ s) = (0 : M)
    · refine ⟨⟨26,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
    · refine ⟨⟨23,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
  · by_cases hz : getSem 6 (pi₂ s) = (0 : M)
    · refine ⟨⟨25,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
    · refine ⟨⟨24,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
  · refine ⟨⟨22,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · refine ⟨⟨27,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · by_cases hz : getSem 6 (pi₂ s) = (0 : M)
    · refine ⟨⟨32,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
    · refine ⟨⟨27,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
  · by_cases hz : getSem 5 (pi₂ s) = (0 : M)
    · refine ⟨⟨29,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
    · refine ⟨⟨28,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
  · refine ⟨⟨27,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · by_cases hz : getSem 6 (pi₂ s) = (0 : M)
    · refine ⟨⟨31,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
    · refine ⟨⟨30,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
  · refine ⟨⟨27,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · refine ⟨⟨34,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]
  · by_cases hz : getSem 1 (pi₂ s) = (0 : M)
    · refine ⟨⟨34,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
    · refine ⟨⟨33,by decide⟩,?_⟩
      simp [gateData,instructionSem,destination,hz]
  · refine ⟨⟨32,by decide⟩,?_⟩
    simp [gateData,instructionSem,destination]

#print axioms next_index
end models
end PA194AX11HGateNext
