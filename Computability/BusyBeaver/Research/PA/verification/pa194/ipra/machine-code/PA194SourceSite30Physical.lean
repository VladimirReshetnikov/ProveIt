import PA194SourceSite29Controller
import PA194Site30Jump
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite30Physical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite25Physical
open PA194RegisterPermutation PA194RegisterFile

theorem site30Instruction :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 30).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) =
        some (.jump (some 27)) := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem sourcePhysical (k tail : M) (args : Fin 11 → M) :
    F step ![sourceState 30 args tail] = sourceState 27 args tail ∧
    F PA194Stepper.stepper ![modelNumeral M 40,physicalFrame 30 ((k+1)+1) args] =
      physicalFrame 27 ((((k+1)+1)+1)+1) args := by
  have hpc : F pc ![sourceState 30 args tail] = modelNumeral M 30 := by
    rw [pcModel]
    exact pi₁_pair _ _
  constructor
  · rw [actualInstructionStep 30 (by decide) _ hpc,site30Instruction]
    change pair (modelNumeral M 27) (pi₂ (pair (modelNumeral M 30) (pack (regsOfArgs args) tail))) = _
    rw [pi₂_pair]
    rfl
  · exact PA194Site30Jump.jumpPath30To27 k (F sourceFileCode args)
#print axioms site30Instruction
#print axioms sourcePhysical
end models
end PA194SourceSite30Physical
