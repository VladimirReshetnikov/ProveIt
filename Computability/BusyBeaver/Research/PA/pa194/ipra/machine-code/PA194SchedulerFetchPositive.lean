import PA194SourceControllerStep
import PA194SourceRegisterRelation
import PA194SourcePCBound
import PA194SchedulerCode
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SchedulerFetchPositive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound
open PA194SchedulerCode

theorem site26Instruction :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 26).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) =
        some (.jump (some 34)) := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

def regsOfArgs (args : Fin 11 → M) (i : Fin 9) : M := args ⟨i.val,by have h := i.isLt; omega⟩
noncomputable def sourceState (q : Nat) (args : Fin 11 → M) (tail : M) : M :=
  pair (modelNumeral M q) (pack (regsOfArgs args) tail)

theorem updateRegister8 (args : Fin 11 → M) (tail m : M) :
    putSem 8 (pack (regsOfArgs args) tail) m =
      pack (regsOfArgs (Function.update args 8 m)) tail := by
  simp [putSem,PA194SourceRegisterRelation.pack,regsOfArgs,pi₁_pair,pi₂_pair,Function.update]

theorem sourcePositive25 (args : Fin 11 → M) (tail m : M) (hm : args 8=m+1) :
    F step ![sourceState 25 args tail] = sourceState 26 (Function.update args 8 m) tail := by
  have hpc : F pc ![sourceState 25 args tail] = modelNumeral M 25 := by
    rw [pcModel]
    exact pi₁_pair _ _
  have hreg : getSem 8 (pi₂ (sourceState 25 args tail)) = args 8 := by
    change getSem 8 (pi₂ (pair (modelNumeral M 25) (pack (regsOfArgs args) tail))) = args 8
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs args) tail (8 : Fin 9)
    change getSem 8 (pack (regsOfArgs args) tail) = args 8 at h
    exact h
  have hnonzero : getSem 8 (pi₂ (sourceState 25 args tail)) ≠ (0 : M) := by
    rw [hreg,hm]
    exact ne_of_gt (lt_of_le_of_lt (zero_le : (0 : M) ≤ m) (lt_add_of_pos_right m (Arithmetic.zero_lt_one : (0 : M) < 1)))
  have hpred : F predCode (fun _ => getSem 8 (pi₂ (sourceState 25 args tail))) = m := by
    rw [hreg,hm,show m+1 = F Code.succ (fun _ => m) from modelAddOne m,modelPredSucc]
  rw [site25Positive _ hpc hnonzero,hpred]
  change pair (modelNumeral M 26) (putSem 8 (pi₂ (pair (modelNumeral M 25)
    (pack (regsOfArgs args) tail))) m) = _
  rw [pi₂_pair,updateRegister8]
  rfl

theorem positiveFields (n m : M) :
    F (fetchSeed (.proj 0) (.proj 1)) ![n,m+1] = m ∧
    F (nextN (.proj 0) (.proj 1)) ![n,m+1] = n := by
  have hn : m+1 ≠ (0 : M) := ne_of_gt (lt_of_le_of_lt (zero_le : (0 : M) ≤ m)
    (lt_add_of_pos_right m (Arithmetic.zero_lt_one : (0 : M) < 1)))
  constructor
  · rw [fetchSeed,choose0_model]
    simp only [modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one,hn,if_false]
    rw [PA194PathIterator.modelUnary,modelProjection]
    change F predCode (fun _ => m+1) = m
    rw [show m+1 = F Code.succ (fun _ => m) from modelAddOne m,modelPredSucc]
  · rw [nextN,choose0_model]
    simp only [modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one,hn,if_false]

theorem sourceJump26 (args : Fin 11 → M) (tail : M) :
    F step ![sourceState 26 args tail] = sourceState 34 args tail := by
  have hpc : F pc ![sourceState 26 args tail] = modelNumeral M 26 := by
    rw [pcModel]
    exact pi₁_pair _ _
  rw [actualInstructionStep 26 (by decide) _ hpc,site26Instruction]
  change pair (modelNumeral M 34) (pi₂ (pair (modelNumeral M 26) (pack (regsOfArgs args) tail))) = _
  rw [pi₂_pair]
  rfl

theorem positiveFetchPrefix (args : Fin 11 → M) (tail m : M) (hm : args 8 = m+1) :
    F step ![F step ![sourceState 25 args tail]] = sourceState 34 (Function.update args 8 m) tail ∧
    F (fetchSeed (.proj 0) (.proj 1)) ![args 0,args 8] = m ∧
    F (nextN (.proj 0) (.proj 1)) ![args 0,args 8] = args 0 := by
  have hsource := sourcePositive25 args tail m hm
  refine ⟨?_,?_,?_⟩
  · rw [hsource,sourceJump26]
  · rw [hm]; exact (positiveFields (args 0) m).1
  · rw [hm]; exact (positiveFields (args 0) m).2
#print axioms site26Instruction
#print axioms updateRegister8
#print axioms sourcePositive25
#print axioms positiveFields
#print axioms sourceJump26
#print axioms positiveFetchPrefix
end models
end PA194SchedulerFetchPositive
