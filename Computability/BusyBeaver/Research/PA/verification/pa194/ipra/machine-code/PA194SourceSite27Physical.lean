import PA194Site25FrameRelation
import PA194Path27To28
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite27Physical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite25Physical PA194Site25FrameRelation

theorem site27Instruction :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 27).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) =
        some (.dec 0 (some 31) (some 28)) := by decide +kernel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem updateRegister0 (args : Fin 11 → M) (tail m : M) :
    putSem 0 (pack (regsOfArgs args) tail) m =
      pack (regsOfArgs (Function.update args 0 m)) tail := by
  simp [putSem,PA194SourceRegisterRelation.pack,regsOfArgs,pi₂_pair,Function.update]

/-- Register 0 positive: both the encoded source state and the literal
    physical frame advance from site 27 to 28. -/
theorem positiveBranch (k tail m : M) (args : Fin 11 → M) (hm : args 0 = m+1) :
    F step ![sourceState 27 args tail] = sourceState 28 (Function.update args 0 m) tail ∧
      ∃ clock : M, F PA194Stepper.stepper ![clock,physicalFrame 27 ((k+1)+1) args] =
        physicalFrame 28 ((k+1)+1) (Function.update args 0 m) := by
  have hpc : F pc ![sourceState 27 args tail] = modelNumeral M 27 := by
    rw [pcModel]
    exact pi₁_pair _ _
  have hreg : getSem 0 (pi₂ (sourceState 27 args tail)) = args 0 := by
    change getSem 0 (pi₂ (pair (modelNumeral M 27) (pack (regsOfArgs args) tail))) = args 0
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs args) tail (0 : Fin 9)
    change getSem 0 (pack (regsOfArgs args) tail) = args 0 at h
    exact h
  have hnonzero : getSem 0 (pi₂ (sourceState 27 args tail)) ≠ (0 : M) := by
    rw [hreg,hm]
    exact ne_of_gt (lt_of_le_of_lt (zero_le : (0 : M) ≤ m) (lt_add_of_pos_right m (Arithmetic.zero_lt_one : (0 : M) < 1)))
  have hpred : F predCode (fun _ => getSem 0 (pi₂ (sourceState 27 args tail))) = m := by
    rw [hreg,hm,show m+1 = F Code.succ (fun _ => m) from modelAddOne m,modelPredSucc]
  constructor
  · rw [actualInstructionStep 27 (by decide) _ hpc,site27Instruction]
    simp only [PA194SourceInstructionModel.instructionSem,destination]
    change (if getSem 0 (pi₂ (sourceState 27 args tail)) = (0 : M) then _ else _) = _
    rw [if_neg hnonzero]
    change pair (modelNumeral M 28) (putSem 0 (pi₂ (sourceState 27 args tail))
      (F predCode (fun _ => getSem 0 (pi₂ (sourceState 27 args tail))))) = _
    rw [hpred]
    change pair (modelNumeral M 28) (putSem 0 (pi₂ (pair (modelNumeral M 27)
      (pack (regsOfArgs args) tail))) m) = _
    rw [pi₂_pair,updateRegister0]
    rfl
  · exact ⟨_, PA194Path27To28.positiveBranchPath27To28 k m args hm⟩

def MatchedPositive27 (gap source physical : M) : Prop :=
  ∃ (args : Fin 11 → M) (tail m : M),
    source = sourceState 27 args tail ∧ physical = physicalFrame 27 gap args ∧ args 0 = m+1

theorem matchedPositiveStep (k source physical : M)
    (h : MatchedPositive27 ((k+1)+1) source physical) :
    ∃ clock nextPhysical : M,
      F PA194Stepper.stepper ![clock,physical] = nextPhysical ∧
        Matched 28 ((k+1)+1) (F step ![source]) nextPhysical := by
  obtain ⟨args,tail,m,rfl,rfl,hm⟩ := h
  obtain ⟨hsource,clock,hphysical⟩ := positiveBranch k tail m args hm
  exact ⟨clock,physicalFrame 28 ((k+1)+1) (Function.update args 0 m),hphysical,
    Function.update args 0 m,tail,hsource,rfl⟩
#print axioms site27Instruction
#print axioms updateRegister0
#print axioms positiveBranch
#print axioms matchedPositiveStep
end models
end PA194SourceSite27Physical
