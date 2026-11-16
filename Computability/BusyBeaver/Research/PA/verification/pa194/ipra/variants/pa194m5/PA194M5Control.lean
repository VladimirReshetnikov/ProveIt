import PA194ProgramControl
import PA194M5Program

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194M5Control
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194ProgramControl PA194M5Program
open PA194SourceControllerCode (pc)
open PA194SchedulerFetchPositive (sourceState regsOfArgs)
open PA194SourceFetchLoop (statePC)
open PA194SourceRegisterRelation (pack)
open PA194IteratedSimulation PA194ClockInvariantDefinable PRAExhaustion

theorem malformedOrdinal : malformed program = 3734 := programLength
theorem haltedOrdinal : halted program = 3735 := by rw [halted,programLength]
theorem haltRow : PA194ProgramDrain.row program 10 = some .halt := by decide +kernel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem haltExecution (args : Fin 11 → M) (tail : M) :
    F (PA194ProgramControl.step program) ![sourceState 10 args tail] =
      sourceState 3735 args tail := by
  rw [haltStep program 10 (by rw [programLength]; decide) _ (statePC _ _ _) haltRow,haltedOrdinal]
  change pair (modelNumeral M 3735) (pi₂ (pair (modelNumeral M 10) (pack (regsOfArgs args) tail))) = _
  rw [pi₂_pair]; rfl

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem iterateFixed (next : Code 1) (s : M) (h : F next ![s] = s) :
    ∀ c : M, F (iterate next) ![c,s] = s := by
  haveI : 𝚺₁-Function₁ (fun c : M => F (iterate next) ![c,s]) :=
    bindBinary _ s (binaryCodeDef (M := M) (iterate next))
  have hdef : 𝚺₁-Predicate (fun c : M => F (iterate next) ![c,s] = s) := by definability
  intro c
  induction c using ISigma1.sigma1_succ_induction with
  | hP => exact hdef
  | zero => exact iterateZero next s
  | succ c ih => rw [iterateSucc, ih, h]

theorem haltedRun (s : M) (hs : F pc ![s] = modelNumeral M 3735) :
    ∀ c : M, F (PA194ProgramControl.run program) ![c,s] = s := by
  apply iterateFixed
  apply haltedFixed
  rwa [haltedOrdinal]

theorem malformedRun (s : M) (hs : F pc ![s] = modelNumeral M 3734) :
    ∀ c : M, F (PA194ProgramControl.run program) ![c,s] = s := by
  apply iterateFixed
  apply malformedFixed
  rwa [malformedOrdinal]

#print axioms haltRow
#print axioms haltExecution
#print axioms haltedRun
#print axioms malformedRun

end models
end PA194M5Control
