import PA194SourceControllerSites
import PA194SourceInstructionModel
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourceControllerStep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourceControllerBinding PA194SourceControllerSites
open PA194SourceRegisters PA194SourceInstructionModel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem actualInstructionStep (i : Nat) (hi : i < 3673) (s : M)
    (hs : F pc ![s] = modelNumeral M i) :
    F step ![s] = instructionSem
      ((M6.Source.PathTrie.nthSite PA194.SourceTree.trie i).bind
        (M6.FastResolve.resolveTree PA194.SourceTree.trie)) s := by
  rw [selectActual i hi s hs,instructionModel]

theorem site10Step (s : M) (hs : F pc ![s] = modelNumeral M 10) :
    F step ![s] = pair (modelNumeral M 3674) (pi₂ s) := by
  rw [selectSite10 s hs,instructionModel]
  rfl

theorem site25Zero (s : M) (hs : F pc ![s] = modelNumeral M 25)
    (hz : getSem 8 (pi₂ s) = (0 : M)) :
    F step ![s] = pair (modelNumeral M 27) (pi₂ s) := by
  rw [selectSite25 s hs,instructionModel]
  simp only [instructionSem,destination]
  change (if getSem 8 (pi₂ s) = (0 : M) then _ else _) = _
  rw [if_pos hz]

theorem site25Positive (s : M) (hs : F pc ![s] = modelNumeral M 25)
    (hn : getSem 8 (pi₂ s) ≠ (0 : M)) :
    F step ![s] = pair (modelNumeral M 26)
      (putSem 8 (pi₂ s) (F predCode (fun _ => getSem 8 (pi₂ s)))) := by
  rw [selectSite25 s hs,instructionModel]
  simp only [instructionSem,destination]
  change (if getSem 8 (pi₂ s) = (0 : M) then _ else _) = _
  rw [if_neg hn]
  rfl
#print axioms actualInstructionStep
#print axioms site10Step
#print axioms site25Zero
#print axioms site25Positive
end models
end PA194SourceControllerStep
