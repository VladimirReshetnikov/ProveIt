import PA194SourceSite31Controller
import PA194SourceControllerStep
import PA194SourceRegisterRelation
import PA194SourcePCBound
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite35Controller
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite31Controller

theorem site35Instruction :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 35).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) =
        some (.inc 7 (some 36)) := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

def updated (args : Fin 11 → M) (suffix : M) : Fin 11 → M :=
  Function.update (Function.update args 7 (args 7+1)) 10 suffix

theorem updateRegister7 (args : Fin 11 → M) (tail m : M) :
    putSem 7 (pack (regsOfArgs args) tail) m =
      pack (regsOfArgs (Function.update args 7 m)) tail := by
  simp [putSem,PA194SourceRegisterRelation.pack,regsOfArgs,pi₁_pair,pi₂_pair,Function.update]

theorem updatedRegs (args : Fin 11 → M) (suffix : M) :
    regsOfArgs (updated args suffix) =
      regsOfArgs (Function.update args 7 (args 7+1)) := by
  funext i
  fin_cases i <;> simp [regsOfArgs,updated]

theorem controllerStep (args : Fin 11 → M) (tail suffix : M) :
    F step ![sourceState 35 args tail] = sourceState 36 (updated args suffix) tail := by
  have hpc : F pc ![sourceState 35 args tail] = modelNumeral M 35 := by
    rw [pcModel]
    exact pi₁_pair _ _
  have hreg : getSem 7 (pi₂ (sourceState 35 args tail)) = args 7 := by
    change getSem 7 (pi₂ (pair (modelNumeral M 35) (pack (regsOfArgs args) tail))) = args 7
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs args) tail (7 : Fin 9)
    change getSem 7 (pack (regsOfArgs args) tail) = args 7 at h
    exact h
  rw [actualInstructionStep 35 (by decide) _ hpc,site35Instruction]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change pair (modelNumeral M 36) (putSem 7 (pi₂ (sourceState 35 args tail))
    (F Code.succ (fun _ => getSem 7 (pi₂ (sourceState 35 args tail))))) = _
  rw [hreg,←modelAddOne]
  change pair (modelNumeral M 36) (putSem 7 (pi₂ (pair (modelNumeral M 35)
    (pack (regsOfArgs args) tail))) (args 7+1)) = _
  rw [pi₂_pair,updateRegister7]
  change pair (modelNumeral M 36) (pack (regsOfArgs (Function.update args 7 (args 7+1))) tail) =
    pair (modelNumeral M 36) (pack (regsOfArgs (updated args suffix)) tail)
  rw [updatedRegs]
#print axioms site35Instruction
#print axioms updateRegister7
#print axioms updatedRegs
#print axioms controllerStep
end models
end PA194SourceSite35Controller
