import PA194SourceSite25Positive
import PA194Site28Complete
import PA194Site25FrameRelation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite28Physical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite25Physical
open PA194Site28Complete PA194Site28OutputFile PA194Site28SeedRoundTrip

theorem site28Instruction :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 28).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) =
        some (.inc 8 (some 29)) := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem updatedRegs (args : Fin 11 → M) :
    regsOfArgs (updated args) = regsOfArgs (Function.update args 8 (args 8+1)) := by
  funext i
  fin_cases i <;> simp [regsOfArgs,updated]

theorem controllerStep (args : Fin 11 → M) (tail : M) :
    F step ![sourceState 28 args tail] = sourceState 29 (updated args) tail := by
  have hpc : F pc ![sourceState 28 args tail] = modelNumeral M 28 := by
    rw [pcModel]
    exact pi₁_pair _ _
  have hreg : getSem 8 (pi₂ (sourceState 28 args tail)) = args 8 := by
    change getSem 8 (pi₂ (pair (modelNumeral M 28) (pack (regsOfArgs args) tail))) = args 8
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs args) tail (8 : Fin 9)
    change getSem 8 (pack (regsOfArgs args) tail) = args 8 at h
    exact h
  rw [actualInstructionStep 28 (by decide) _ hpc,site28Instruction]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change pair (modelNumeral M 29) (putSem 8 (pi₂ (sourceState 28 args tail))
    (F Code.succ (fun _ => getSem 8 (pi₂ (sourceState 28 args tail))))) = _
  rw [hreg,←modelAddOne]
  change pair (modelNumeral M 29) (putSem 8 (pi₂ (pair (modelNumeral M 28)
    (pack (regsOfArgs args) tail))) (args 8+1)) = _
  rw [pi₂_pair,PA194SourceSite25Positive.updateRegister8]
  change pair (modelNumeral M 29) (pack (regsOfArgs (Function.update args 8 (args 8+1))) tail) =
    pair (modelNumeral M 29) (pack (regsOfArgs (updated args)) tail)
  rw [updatedRegs]

theorem sourcePhysicalNested (k tail : M) (args : Fin 11 → M)
    (htail : args 10 = modelNumeral M PA194StartupSourceFrame.seedTail) :
    F step ![sourceState 28 args tail] = sourceState 29 (updated args) tail ∧
    finishRun k args (seedRun (args 9) (F PA194Stepper.stepper ![rootClock k args,
      physicalFrame 28 ((k+1)+1) args])) = physicalFrame 29 (k+1) (updated args) := by
  refine ⟨controllerStep args tail,?_⟩
  exact PA194Site28Complete.complete k args htail
/-- Collapse all the explicitly coded machine segments to one model-valued time. -/
theorem physicalClock (k : M) (args : Fin 11 → M) (x : M) :
    ∃ clock : M, F PA194Stepper.stepper ![clock,x] =
      finishRun k args (seedRun (args 9) (F PA194Stepper.stepper ![rootClock k args,x])) := by
  simp only [finishRun,seedRun,←PA194StepperCompose.modelStepperCompose]
  exact ⟨_,rfl⟩

theorem sourcePhysical (k tail : M) (args : Fin 11 → M)
    (htail : args 10 = modelNumeral M PA194StartupSourceFrame.seedTail) :
    F step ![sourceState 28 args tail] = sourceState 29 (updated args) tail ∧
    ∃ clock : M, F PA194Stepper.stepper ![clock,physicalFrame 28 ((k+1)+1) args] =
      physicalFrame 29 (k+1) (updated args) := by
  obtain ⟨hs,hphysical⟩ := sourcePhysicalNested k tail args htail
  obtain ⟨clock,hclock⟩ := physicalClock k args (physicalFrame 28 ((k+1)+1) args)
  exact ⟨hs,clock,hclock.trans hphysical⟩

/-- Matching relation with the specific fixed suffix needed at site 28. -/
def SeedMatched (gap source physical : M) : Prop :=
  ∃ (args : Fin 11 → M) (tail : M),
    source = sourceState 28 args tail ∧ physical = physicalFrame 28 gap args ∧
      args 10 = modelNumeral M PA194StartupSourceFrame.seedTail

theorem matchedStep (k source physical : M) (h : SeedMatched ((k+1)+1) source physical) :
    ∃ clock nextPhysical : M,
      F PA194Stepper.stepper ![clock,physical] = nextPhysical ∧
        PA194Site25FrameRelation.Matched 29 (k+1) (F step ![source]) nextPhysical := by
  obtain ⟨args,tail,rfl,rfl,htail⟩ := h
  obtain ⟨hs,clock,hphysical⟩ := sourcePhysical k tail args htail
  exact ⟨clock,physicalFrame 29 (k+1) (updated args),hphysical,updated args,tail,hs,rfl⟩
#print axioms site28Instruction
#print axioms updatedRegs
#print axioms controllerStep
#print axioms sourcePhysicalNested
#print axioms physicalClock
#print axioms sourcePhysical
#print axioms matchedStep
end models
end PA194SourceSite28Physical
