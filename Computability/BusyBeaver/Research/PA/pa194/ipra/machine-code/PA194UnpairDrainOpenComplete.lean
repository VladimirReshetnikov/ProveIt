import PA194UnpairDrainOpen
import PA194IterateAddOpen
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194UnpairDrainOpenComplete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASubAddition
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SchedulerFetchPositive PA194SourceFetchLoop PA194SourceFetchRestoreLoop PA194UnpairRound
open PA194IteratedSimulation PA194ClockInvariantDefinable PA194ControllerRunAdd PA194UnpairDrainLoop PA194UnpairDrainOpen PA194UnpairDrainOpen PA194IterateAddOpen
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem subSelf (x : M) : F subCode ![x,x] = (0 : M) := by
  have h := modelSubAdd x (0 : M)
  change F subCode ![x+0,x] = (0 : M) at h
  simpa only [add_zero] using h

theorem drainComplete (args : Fin 11 → M) (tail : M) :
    let n := args 7
    let out := PA194UnpairDrainOpen.argsAt args n
    F run ![(three n+1)+1,sourceState 38 args tail] = sourceState 34 out tail := by
  let n := args 7
  let out := PA194UnpairDrainOpen.argsAt args n
  have hz : out 7 = (0 : M) := by simp [out,n,PA194UnpairDrainOpen.argsAt,subSelf]
  have hrun := PA194UnpairDrainOpen.runDrain args tail n (le_refl n)
  change F run ![three n,sourceState 38 args tail] = sourceState 38 out tail at hrun
  have hexit := drainExit out tail hz
  change F (iterate step) ![(three n+1)+1,sourceState 38 args tail] = _
  rw [PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterSucc]
  change F step ![F step ![F run ![three n,sourceState 38 args tail]]] = _
  rw [hrun,hexit]
theorem zeroXRound (args : Fin 11 → M) (tail w : M)
    (hw : args 8 = w+1) (hx : args 6 = (0 : M)) :
    let a1 := Function.update args 8 w
    let a2 := Function.update a1 7 (a1 7+1)
    let out := PA194UnpairDrainOpen.argsAt a2 (a2 7)
    F run ![(((0 : M)+1)+1)+1 + ((three (a2 7)+1)+1),sourceState 34 args tail] = sourceState 34 out tail ∧
    out 8 = w ∧ out 6 = args 7+1 ∧ out 7 = 0 ∧
    ∀ i : Fin 11, i ≠ 6 → i ≠ 7 → i ≠ 8 → out i = args i := by
  let a1 := Function.update args 8 w
  let a2 := Function.update a1 7 (a1 7+1)
  let out := PA194UnpairDrainOpen.argsAt a2 (a2 7)
  have h34 := sourceDecPositive 34 35 8 (some 42) (by decide) inst34 args tail w hw
  have h35 := sourceInc 35 36 7 (by decide) inst35 a1 tail
  have hz : regsOfArgs a2 6 = (0 : M) := by simp [regsOfArgs,a2,a1,hx]
  have h36 := sourceDecZero 36 38 6 (some 37) (by decide) inst36 a2 tail hz
  change F step ![sourceState 34 args tail] = sourceState 35 a1 tail at h34
  change F step ![sourceState 35 a1 tail] = sourceState 36 a2 tail at h35
  have hstart : F (iterate step) ![(((0 : M)+1)+1)+1,sourceState 34 args tail] = sourceState 38 a2 tail := by
    rw [PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterZero,h34,h35,h36]
  have hend := drainComplete a2 tail
  change F run ![(three (a2 7)+1)+1,sourceState 38 a2 tail] = sourceState 34 out tail at hend
  refine ⟨?_,?_,?_,?_,?_⟩
  · change F (iterate step) ![(((0 : M)+1)+1)+1 + ((three (a2 7)+1)+1),sourceState 34 args tail] = _
    rw [PA194IterateAddOpen.iterateAdd,hstart]
    exact hend
  · simp [out,PA194UnpairDrainOpen.argsAt,a2,a1]
  · simp [out,PA194UnpairDrainOpen.argsAt,a2,a1,hx]
  · simp [out,PA194UnpairDrainOpen.argsAt,subSelf]
  · intro i h6 h7 h8
    simp [out,PA194UnpairDrainOpen.argsAt,a2,a1,Function.update_of_ne h6,Function.update_of_ne h7,Function.update_of_ne h8]
#print axioms zeroXRound
#print axioms drainComplete
end models
end PA194UnpairDrainOpenComplete
