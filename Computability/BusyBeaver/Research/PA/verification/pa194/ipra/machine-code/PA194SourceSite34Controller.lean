import PA194SourceSite31Controller
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite34Controller
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite31Controller

theorem site34Instruction :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 34).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) =
        some (.dec 8 (some 42) (some 35)) := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem zeroBranch (args : Fin 11 → M) (tail : M) (hz : args 8 = (0 : M)) :
    F step ![sourceState 34 args tail] = sourceState 42 args tail := by
  have hpc : F pc ![sourceState 34 args tail] = modelNumeral M 34 := by
    rw [pcModel]; exact pi₁_pair _ _
  have hreg : getSem 8 (pi₂ (sourceState 34 args tail)) = args 8 := by
    change getSem 8 (pi₂ (pair (modelNumeral M 34) (pack (regsOfArgs args) tail))) = args 8
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs args) tail (8 : Fin 9)
    change getSem 8 (pack (regsOfArgs args) tail) = args 8 at h
    exact h
  rw [actualInstructionStep 34 (by decide) _ hpc,site34Instruction]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change (if getSem 8 (pi₂ (sourceState 34 args tail)) = (0 : M) then _ else _) = _
  rw [if_pos (hreg.trans hz)]
  change pair (modelNumeral M 42) (pi₂ (pair (modelNumeral M 34) (pack (regsOfArgs args) tail))) = _
  rw [pi₂_pair]
  rfl

#print axioms site34Instruction
#print axioms zeroBranch
end models
end PA194SourceSite34Controller
