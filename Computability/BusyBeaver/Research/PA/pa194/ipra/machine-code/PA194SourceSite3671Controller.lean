import PA194SourceSite31Controller
import PA194SourceControllerStep
import PA194SourceRegisterRelation
import PA194SourcePCBound
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite3671Controller
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite31Controller

theorem site3671Instruction :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 3671).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) =
        some (.inc 6 (some 3672)) := by decide +kernel
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
  Function.update (Function.update args 6 (args 6+1)) 10 suffix

theorem updateRegister6 (args : Fin 11 → M) (tail m : M) :
    putSem 6 (pack (regsOfArgs args) tail) m =
      pack (regsOfArgs (Function.update args 6 m)) tail := by
  simp [putSem,PA194SourceRegisterRelation.pack,regsOfArgs,pi₁_pair,pi₂_pair,Function.update]

theorem updatedRegs (args : Fin 11 → M) (suffix : M) :
    regsOfArgs (updated args suffix) =
      regsOfArgs (Function.update args 6 (args 6+1)) := by
  funext i
  fin_cases i <;> simp [regsOfArgs,updated]

theorem controllerStep (args : Fin 11 → M) (tail suffix : M) :
    F step ![sourceState 3671 args tail] = sourceState 3672 (updated args suffix) tail := by
  have hpc : F pc ![sourceState 3671 args tail] = modelNumeral M 3671 := by
    rw [pcModel]
    exact pi₁_pair _ _
  have hreg : getSem 6 (pi₂ (sourceState 3671 args tail)) = args 6 := by
    change getSem 6 (pi₂ (pair (modelNumeral M 3671) (pack (regsOfArgs args) tail))) = args 6
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs args) tail (6 : Fin 9)
    change getSem 6 (pack (regsOfArgs args) tail) = args 6 at h
    exact h
  rw [actualInstructionStep 3671 (by decide) _ hpc,site3671Instruction]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change pair (modelNumeral M 3672) (putSem 6 (pi₂ (sourceState 3671 args tail))
    (F Code.succ (fun _ => getSem 6 (pi₂ (sourceState 3671 args tail))))) = _
  rw [hreg,←modelAddOne]
  change pair (modelNumeral M 3672) (putSem 6 (pi₂ (pair (modelNumeral M 3671)
    (pack (regsOfArgs args) tail))) (args 6+1)) = _
  rw [pi₂_pair,updateRegister6]
  change pair (modelNumeral M 3672) (pack (regsOfArgs (Function.update args 6 (args 6+1))) tail) =
    pair (modelNumeral M 3672) (pack (regsOfArgs (updated args suffix)) tail)
  rw [updatedRegs]
#print axioms site3671Instruction
#print axioms updateRegister6
#print axioms updatedRegs
#print axioms controllerStep
end models
end PA194SourceSite3671Controller
