import PA194SourceSite31Controller
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite3672Controller
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite31Controller

theorem site3672Instruction :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 3672).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) =
        some (.jump (some 0)) := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem controllerStep (args : Fin 11 → M) (tail : M) :
    F step ![sourceState 3672 args tail] = sourceState 0 args tail := by
  have hpc : F pc ![sourceState 3672 args tail] = modelNumeral M 3672 := by
    rw [pcModel]
    exact pi₁_pair _ _
  rw [actualInstructionStep 3672 (by decide) _ hpc,site3672Instruction]
  change pair (modelNumeral M 0) (pi₂ (pair (modelNumeral M 3672) (pack (regsOfArgs args) tail))) = _
  rw [pi₂_pair]
  rfl
#print axioms site3672Instruction
#print axioms controllerStep
end models
end PA194SourceSite3672Controller
