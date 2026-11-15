import PA194SourceSite27Physical
import PA194Site27ZeroPath
import PA194Site27ZeroFile
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite27Zero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite25Physical PA194Site25FrameRelation
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem zeroBranch (k tail : M) (args : Fin 11 → M) (hz : args 0 = (0 : M)) :
    F step ![sourceState 27 args tail] = sourceState 31 args tail ∧
      ∃ clock : M, F PA194Stepper.stepper ![clock,physicalFrame 27 ((k+1)+1) args] =
        physicalFrame 31 ((k+1)+1) args := by
  have hpc : F pc ![sourceState 27 args tail] = modelNumeral M 27 := by
    rw [pcModel]
    exact pi₁_pair _ _
  have hreg : getSem 0 (pi₂ (sourceState 27 args tail)) = args 0 := by
    change getSem 0 (pi₂ (pair (modelNumeral M 27) (pack (regsOfArgs args) tail))) = args 0
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs args) tail (0 : Fin 9)
    change getSem 0 (pack (regsOfArgs args) tail) = args 0 at h
    exact h
  constructor
  · rw [actualInstructionStep 27 (by decide) _ hpc,PA194SourceSite27Physical.site27Instruction]
    simp only [PA194SourceInstructionModel.instructionSem,destination]
    change (if getSem 0 (pi₂ (sourceState 27 args tail)) = (0 : M) then _ else _) = _
    rw [if_pos (hreg.trans hz)]
    change pair (modelNumeral M 31) (pi₂ (pair (modelNumeral M 27) (pack (regsOfArgs args) tail))) = _
    rw [pi₂_pair]
    rfl
  · exact PA194Site27ZeroPath.zeroBranchWithFile k args hz (PA194Site27ZeroFile.returnedIsSourceFile args hz)

theorem matchedStep (k source physical : M)
    (h : Matched 27 ((k+1)+1) source physical) :
    ∃ clock nextPhysical : M,
      F PA194Stepper.stepper ![clock,physical] = nextPhysical ∧
        (Matched 31 ((k+1)+1) (F step ![source]) nextPhysical ∨
         Matched 28 ((k+1)+1) (F step ![source]) nextPhysical) := by
  classical
  obtain ⟨args,tail,rfl,rfl⟩ := h
  by_cases hz : args 0 = (0 : M)
  · obtain ⟨hsource,clock,hphysical⟩ := zeroBranch k tail args hz
    exact ⟨clock,physicalFrame 31 ((k+1)+1) args,hphysical,Or.inl ⟨args,tail,hsource,rfl⟩⟩
  · let m := F predCode (fun _ => args 0)
    have hsucc : F Code.succ (fun _ => m) = args 0 :=
      (modelZeroOrSuccPred (args 0)).resolve_left hz
    have hm : args 0 = m+1 := hsucc.symm.trans (modelAddOne m).symm
    obtain ⟨hsource,clock,hphysical⟩ := PA194SourceSite27Physical.positiveBranch k tail m args hm
    exact ⟨clock,physicalFrame 28 ((k+1)+1) (Function.update args 0 m),hphysical,
      Or.inr ⟨Function.update args 0 m,tail,hsource,rfl⟩⟩
#print axioms zeroBranch
#print axioms matchedStep
end models
end PA194SourceSite27Zero
