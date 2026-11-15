import PA194SourceSite28Physical
import PA194Site28DynamicComplete
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite28DynamicPhysical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite25Physical
open PA194Site28Complete PA194Site28DynamicComplete PA194SourceSite28Physical

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem updatedRegs (args : Fin 11 → M) (count : M) :
    regsOfArgs (PA194Site28DynamicOutput.updated args count) = regsOfArgs (Function.update args 8 (args 8+1)) := by
  funext i
  fin_cases i <;> simp [regsOfArgs,PA194Site28DynamicOutput.updated]

theorem controllerStep (args : Fin 11 → M) (tail count : M) :
    F step ![sourceState 28 args tail] = sourceState 29 (PA194Site28DynamicOutput.updated args count) tail := by
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
    pair (modelNumeral M 29) (pack (regsOfArgs (PA194Site28DynamicOutput.updated args count)) tail)
  rw [updatedRegs]

theorem sourcePhysical (k tail count : M) (args : Fin 11 → M)
    (htail : args 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)]) :
    F step ![sourceState 28 args tail] = sourceState 29 (PA194Site28DynamicOutput.updated args count) tail ∧
    ∃ clock : M, F PA194Stepper.stepper ![clock,physicalFrame 28 ((k+1)+1) args] =
      physicalFrame 29 (k+1) (PA194Site28DynamicOutput.updated args count) := by
  have hp := PA194Site28DynamicComplete.complete k count args htail
  dsimp only [PA194Site28DynamicComplete.tailRun, PA194Site28Complete.finishRun] at hp
  simp only [←PA194StepperCompose.modelStepperCompose] at hp
  exact ⟨controllerStep args tail count,_,hp⟩
#print axioms updatedRegs
#print axioms controllerStep
#print axioms sourcePhysical
end models
end PA194SourceSite28DynamicPhysical
