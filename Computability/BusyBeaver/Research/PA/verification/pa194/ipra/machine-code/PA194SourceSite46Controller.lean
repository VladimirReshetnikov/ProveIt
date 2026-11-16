import PA194SourceSite31Controller
import PA194SourceControllerStep
import PA194SourceRegisterRelation
import PA194SourcePCBound
set_option autoImplicit false
set_option maxRecDepth 35536
set_option maxHeartbeats 3000000
namespace PA194SourceSite46Controller
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite31Controller

theorem site46Instruction :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 46).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) =
        some (.inc 3 (some 47)) := by decide +kernel
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
  Function.update (Function.update args 3 (args 3+1)) 10 suffix

theorem updateRegister3 (args : Fin 11 → M) (tail m : M) :
    putSem 3 (pack (regsOfArgs args) tail) m =
      pack (regsOfArgs (Function.update args 3 m)) tail := by
  simp [putSem,PA194SourceRegisterRelation.pack,regsOfArgs,pi₁_pair,pi₂_pair,Function.update]

theorem updatedRegs (args : Fin 11 → M) (suffix : M) :
    regsOfArgs (updated args suffix) =
      regsOfArgs (Function.update args 3 (args 3+1)) := by
  funext i
  fin_cases i <;> simp [regsOfArgs,updated]

theorem controllerStep (args : Fin 11 → M) (tail suffix : M) :
    F step ![sourceState 46 args tail] = sourceState 47 (updated args suffix) tail := by
  have hpc : F pc ![sourceState 46 args tail] = modelNumeral M 46 := by
    rw [pcModel]
    exact pi₁_pair _ _
  have hreg : getSem 3 (pi₂ (sourceState 46 args tail)) = args 3 := by
    change getSem 3 (pi₂ (pair (modelNumeral M 46) (pack (regsOfArgs args) tail))) = args 3
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs args) tail (3 : Fin 9)
    change getSem 3 (pack (regsOfArgs args) tail) = args 3 at h
    exact h
  rw [actualInstructionStep 46 (by decide) _ hpc,site46Instruction]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change pair (modelNumeral M 47) (putSem 3 (pi₂ (sourceState 46 args tail))
    (F Code.succ (fun _ => getSem 3 (pi₂ (sourceState 46 args tail))))) = _
  rw [hreg,←modelAddOne]
  change pair (modelNumeral M 47) (putSem 3 (pi₂ (pair (modelNumeral M 46)
    (pack (regsOfArgs args) tail))) (args 3+1)) = _
  rw [pi₂_pair,updateRegister3]
  change pair (modelNumeral M 47) (pack (regsOfArgs (Function.update args 3 (args 3+1))) tail) =
    pair (modelNumeral M 47) (pack (regsOfArgs (updated args suffix)) tail)
  rw [updatedRegs]
#print axioms site46Instruction
#print axioms updateRegister3
#print axioms updatedRegs
#print axioms controllerStep
end models
end PA194SourceSite46Controller
