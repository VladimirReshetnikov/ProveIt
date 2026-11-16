import PA194SourceSite31Controller
import PA194SourceControllerStep
import PA194SourceRegisterRelation
import PA194SourcePCBound
set_option autoImplicit false
set_option maxRecDepth 85536
set_option maxHeartbeats 8000000
namespace PA194SourceSite43Controller
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite31Controller

theorem site43Instruction :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 43).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) =
        some (.inc 8 (some 44)) := by decide +kernel
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
  Function.update (Function.update args 8 (args 8+1)) 10 suffix

theorem updateRegister8 (args : Fin 11 → M) (tail m : M) :
    putSem 8 (pack (regsOfArgs args) tail) m =
      pack (regsOfArgs (Function.update args 8 m)) tail := by
  simp [putSem,PA194SourceRegisterRelation.pack,regsOfArgs,pi₁_pair,pi₂_pair,Function.update]

theorem updatedRegs (args : Fin 11 → M) (suffix : M) :
    regsOfArgs (updated args suffix) =
      regsOfArgs (Function.update args 8 (args 8+1)) := by
  funext i
  fin_cases i <;> simp [regsOfArgs,updated]

theorem controllerStep (args : Fin 11 → M) (tail suffix : M) :
    F step ![sourceState 43 args tail] = sourceState 44 (updated args suffix) tail := by
  have hpc : F pc ![sourceState 43 args tail] = modelNumeral M 43 := by
    rw [pcModel]
    exact pi₁_pair _ _
  have hreg : getSem 8 (pi₂ (sourceState 43 args tail)) = args 8 := by
    change getSem 8 (pi₂ (pair (modelNumeral M 43) (pack (regsOfArgs args) tail))) = args 8
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs args) tail (8 : Fin 9)
    change getSem 8 (pack (regsOfArgs args) tail) = args 8 at h
    exact h
  rw [actualInstructionStep 43 (by decide) _ hpc,site43Instruction]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change pair (modelNumeral M 44) (putSem 8 (pi₂ (sourceState 43 args tail))
    (F Code.succ (fun _ => getSem 8 (pi₂ (sourceState 43 args tail))))) = _
  rw [hreg,←modelAddOne]
  change pair (modelNumeral M 44) (putSem 8 (pi₂ (pair (modelNumeral M 43)
    (pack (regsOfArgs args) tail))) (args 8+1)) = _
  rw [pi₂_pair,updateRegister8]
  change pair (modelNumeral M 44) (pack (regsOfArgs (Function.update args 8 (args 8+1))) tail) =
    pair (modelNumeral M 44) (pack (regsOfArgs (updated args suffix)) tail)
  rw [updatedRegs]
#print axioms site43Instruction
#print axioms updateRegister8
#print axioms updatedRegs
#print axioms controllerStep
end models
end PA194SourceSite43Controller
