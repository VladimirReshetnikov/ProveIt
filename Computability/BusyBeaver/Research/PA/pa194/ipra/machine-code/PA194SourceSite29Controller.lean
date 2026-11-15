import PA194SourceSite28Physical
import PA194Site29OutputWithCarry
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite29Controller
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite25Physical

theorem site29Instruction :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 29).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) =
        some (.inc 6 (some 30)) := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem updateRegister6 (args : Fin 11 → M) (tail m : M) :
    putSem 6 (pack (regsOfArgs args) tail) m =
      pack (regsOfArgs (Function.update args 6 m)) tail := by
  simp [putSem,PA194SourceRegisterRelation.pack,regsOfArgs,pi₁_pair,pi₂_pair,Function.update]

theorem updatedRegs (args : Fin 11 → M) :
    regsOfArgs (PA194Site29OutputWithCarry.updated args) =
      regsOfArgs (Function.update args 6 (args 6+1)) := by
  funext i
  fin_cases i <;> simp [regsOfArgs,PA194Site29OutputWithCarry.updated]

theorem controllerStep (args : Fin 11 → M) (tail : M) :
    F step ![sourceState 29 args tail] = sourceState 30 (PA194Site29OutputWithCarry.updated args) tail := by
  have hpc : F pc ![sourceState 29 args tail] = modelNumeral M 29 := by
    rw [pcModel]
    exact pi₁_pair _ _
  have hreg : getSem 6 (pi₂ (sourceState 29 args tail)) = args 6 := by
    change getSem 6 (pi₂ (pair (modelNumeral M 29) (pack (regsOfArgs args) tail))) = args 6
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs args) tail (6 : Fin 9)
    change getSem 6 (pack (regsOfArgs args) tail) = args 6 at h
    exact h
  rw [actualInstructionStep 29 (by decide) _ hpc,site29Instruction]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change pair (modelNumeral M 30) (putSem 6 (pi₂ (sourceState 29 args tail))
    (F Code.succ (fun _ => getSem 6 (pi₂ (sourceState 29 args tail))))) = _
  rw [hreg,←modelAddOne]
  change pair (modelNumeral M 30) (putSem 6 (pi₂ (pair (modelNumeral M 29)
    (pack (regsOfArgs args) tail))) (args 6+1)) = _
  rw [pi₂_pair,updateRegister6]
  change pair (modelNumeral M 30) (pack (regsOfArgs (Function.update args 6 (args 6+1))) tail) =
    pair (modelNumeral M 30) (pack (regsOfArgs (PA194Site29OutputWithCarry.updated args)) tail)
  rw [updatedRegs]
#print axioms site29Instruction
#print axioms updateRegister6
#print axioms updatedRegs
#print axioms controllerStep
end models
end PA194SourceSite29Controller
