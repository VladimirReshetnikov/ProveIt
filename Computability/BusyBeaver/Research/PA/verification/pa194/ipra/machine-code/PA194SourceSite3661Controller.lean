import PA194SourceSite31Controller
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite3661Controller
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite31Controller

theorem site3661Instruction :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 3661).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) =
        some (.dec 1 (some 3664) (some 3662)) := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem updateRegister1 (args : Fin 11 → M) (tail m : M) :
    putSem 1 (pack (regsOfArgs args) tail) m =
      pack (regsOfArgs (Function.update args 1 m)) tail := by
  simp [putSem,PA194SourceRegisterRelation.pack,regsOfArgs,pi₁_pair,pi₂_pair,Function.update]

theorem zeroBranch (args : Fin 11 → M) (tail : M) (hz : args 1 = (0 : M)) :
    F step ![sourceState 3661 args tail] = sourceState 3664 args tail := by
  have hpc : F pc ![sourceState 3661 args tail] = modelNumeral M 3661 := by
    rw [pcModel]; exact pi₁_pair _ _
  have hreg : getSem 1 (pi₂ (sourceState 3661 args tail)) = args 1 := by
    change getSem 1 (pi₂ (pair (modelNumeral M 3661) (pack (regsOfArgs args) tail))) = args 1
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs args) tail (1 : Fin 9)
    change getSem 1 (pack (regsOfArgs args) tail) = args 1 at h
    exact h
  rw [actualInstructionStep 3661 (by decide) _ hpc,site3661Instruction]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change (if getSem 1 (pi₂ (sourceState 3661 args tail)) = (0 : M) then _ else _) = _
  rw [if_pos (hreg.trans hz)]
  change pair (modelNumeral M 3664) (pi₂ (pair (modelNumeral M 3661) (pack (regsOfArgs args) tail))) = _
  rw [pi₂_pair]
  rfl

theorem positiveBranch (args : Fin 11 → M) (tail m : M) (hm : args 1 = m+1) :
    F step ![sourceState 3661 args tail] = sourceState 3662 (Function.update args 1 m) tail := by
  have hpc : F pc ![sourceState 3661 args tail] = modelNumeral M 3661 := by
    rw [pcModel]; exact pi₁_pair _ _
  have hreg : getSem 1 (pi₂ (sourceState 3661 args tail)) = args 1 := by
    change getSem 1 (pi₂ (pair (modelNumeral M 3661) (pack (regsOfArgs args) tail))) = args 1
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs args) tail (1 : Fin 9)
    change getSem 1 (pack (regsOfArgs args) tail) = args 1 at h
    exact h
  have hnonzero : getSem 1 (pi₂ (sourceState 3661 args tail)) ≠ (0 : M) := by
    rw [hreg,hm]
    exact ne_of_gt (lt_of_le_of_lt (zero_le : (0 : M) ≤ m) (lt_add_of_pos_right m (Arithmetic.zero_lt_one : (0 : M) < 1)))
  have hpred : F predCode (fun _ => getSem 1 (pi₂ (sourceState 3661 args tail))) = m := by
    rw [hreg,hm,show m+1 = F Code.succ (fun _ => m) from modelAddOne m,modelPredSucc]
  rw [actualInstructionStep 3661 (by decide) _ hpc,site3661Instruction]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change (if getSem 1 (pi₂ (sourceState 3661 args tail)) = (0 : M) then _ else _) = _
  rw [if_neg hnonzero]
  change pair (modelNumeral M 3662) (putSem 1 (pi₂ (sourceState 3661 args tail))
    (F predCode (fun _ => getSem 1 (pi₂ (sourceState 3661 args tail))))) = _
  rw [hpred]
  change pair (modelNumeral M 3662) (putSem 1 (pi₂ (pair (modelNumeral M 3661)
    (pack (regsOfArgs args) tail))) m) = _
  rw [pi₂_pair,updateRegister1]
  rfl
#print axioms site3661Instruction
#print axioms updateRegister1
#print axioms zeroBranch
#print axioms positiveBranch
end models
end PA194SourceSite3661Controller
