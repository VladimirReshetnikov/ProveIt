import PA194SourceSite31Controller
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite49Controller
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite31Controller

theorem site49Instruction :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 49).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) =
        some (.dec 3 (some 3554) (some 50)) := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem updateRegister3 (args : Fin 11 → M) (tail m : M) :
    putSem 3 (pack (regsOfArgs args) tail) m =
      pack (regsOfArgs (Function.update args 3 m)) tail := by
  simp [putSem,PA194SourceRegisterRelation.pack,regsOfArgs,pi₁_pair,pi₂_pair,Function.update]

theorem zeroBranch (args : Fin 11 → M) (tail : M) (hz : args 3 = (0 : M)) :
    F step ![sourceState 49 args tail] = sourceState 3554 args tail := by
  have hpc : F pc ![sourceState 49 args tail] = modelNumeral M 49 := by
    rw [pcModel]; exact pi₁_pair _ _
  have hreg : getSem 3 (pi₂ (sourceState 49 args tail)) = args 3 := by
    change getSem 3 (pi₂ (pair (modelNumeral M 49) (pack (regsOfArgs args) tail))) = args 3
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs args) tail (3 : Fin 9)
    change getSem 3 (pack (regsOfArgs args) tail) = args 3 at h
    exact h
  rw [actualInstructionStep 49 (by decide) _ hpc,site49Instruction]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change (if getSem 3 (pi₂ (sourceState 49 args tail)) = (0 : M) then _ else _) = _
  rw [if_pos (hreg.trans hz)]
  change pair (modelNumeral M 3554) (pi₂ (pair (modelNumeral M 49) (pack (regsOfArgs args) tail))) = _
  rw [pi₂_pair]
  rfl

theorem positiveBranch (args : Fin 11 → M) (tail m : M) (hm : args 3 = m+1) :
    F step ![sourceState 49 args tail] = sourceState 50 (Function.update args 3 m) tail := by
  have hpc : F pc ![sourceState 49 args tail] = modelNumeral M 49 := by
    rw [pcModel]; exact pi₁_pair _ _
  have hreg : getSem 3 (pi₂ (sourceState 49 args tail)) = args 3 := by
    change getSem 3 (pi₂ (pair (modelNumeral M 49) (pack (regsOfArgs args) tail))) = args 3
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs args) tail (3 : Fin 9)
    change getSem 3 (pack (regsOfArgs args) tail) = args 3 at h
    exact h
  have hnonzero : getSem 3 (pi₂ (sourceState 49 args tail)) ≠ (0 : M) := by
    rw [hreg,hm]
    exact ne_of_gt (lt_of_le_of_lt (zero_le : (0 : M) ≤ m) (lt_add_of_pos_right m (Arithmetic.zero_lt_one : (0 : M) < 1)))
  have hpred : F predCode (fun _ => getSem 3 (pi₂ (sourceState 49 args tail))) = m := by
    rw [hreg,hm,show m+1 = F Code.succ (fun _ => m) from modelAddOne m,modelPredSucc]
  rw [actualInstructionStep 49 (by decide) _ hpc,site49Instruction]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change (if getSem 3 (pi₂ (sourceState 49 args tail)) = (0 : M) then _ else _) = _
  rw [if_neg hnonzero]
  change pair (modelNumeral M 50) (putSem 3 (pi₂ (sourceState 49 args tail))
    (F predCode (fun _ => getSem 3 (pi₂ (sourceState 49 args tail))))) = _
  rw [hpred]
  change pair (modelNumeral M 50) (putSem 3 (pi₂ (pair (modelNumeral M 49)
    (pack (regsOfArgs args) tail))) m) = _
  rw [pi₂_pair,updateRegister3]
  rfl
#print axioms site49Instruction
#print axioms updateRegister3
#print axioms zeroBranch
#print axioms positiveBranch
end models
end PA194SourceSite49Controller
