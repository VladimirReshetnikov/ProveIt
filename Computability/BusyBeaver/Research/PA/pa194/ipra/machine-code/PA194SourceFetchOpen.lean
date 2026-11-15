import PA194SourceDrainOpen
import PA194SourceRestoreOpen
import PA194SchedulerFetchFresh
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceFetchOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASubAddition
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceRegisterRelation PA194SchedulerFetchPositive PA194SourceFetchLoop PA194SourceFetchRestoreLoop
open PA194IteratedSimulation PA194ClockInvariantDefinable PA194ControllerRunAdd
open PA194SchedulerCode PA194SchedulerIteration PA194SchedulerPackedFetchPositive PA194SchedulerFetchFresh
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

theorem drainExit (args : Fin 11 → M) (tail : M) :
    let n := args 0
    let out := PA194SourceDrainOpen.argsAt args n
    F PA194SourceControllerCode.run ![PA194SourceDrainOpen.four n+1,sourceState 27 args tail] = sourceState 31 out tail := by
  let n := args 0
  let out := PA194SourceDrainOpen.argsAt args n
  have hz : regsOfArgs out 0 = (0 : M) := by
    simp [regsOfArgs,out,n,PA194SourceDrainOpen.argsAt,subSelf]
  have hstep := sourceDecZero 27 31 0 (some 28) (by decide) inst27 out tail hz
  have hrun := PA194SourceDrainOpen.runDrain args tail n (le_refl n)
  change F PA194SourceControllerCode.run ![PA194SourceDrainOpen.four n,sourceState 27 args tail] = sourceState 27 out tail at hrun
  change F (iterate PA194SourceControllerCode.step) ![PA194SourceDrainOpen.four n+1,sourceState 27 args tail] = _
  rw [PA194DiagonalIteration.iterSucc]
  change F PA194SourceControllerCode.step ![F PA194SourceControllerCode.run ![PA194SourceDrainOpen.four n,sourceState 27 args tail]] = _
  rw [hrun,hstep]

theorem restoreComplete (args : Fin 11 → M) (tail : M) :
    let n := args 6
    let mid := PA194SourceRestoreOpen.argsAt args n
    let out := Function.update mid 0 (mid 0+1)
    F PA194SourceControllerCode.run ![(PA194SourceRestoreOpen.three n+1)+1,sourceState 31 args tail] = sourceState 34 out tail := by
  let n := args 6
  let mid := PA194SourceRestoreOpen.argsAt args n
  have hz : mid 6 = (0 : M) := by simp [mid,n,PA194SourceRestoreOpen.argsAt,subSelf]
  have hrun := PA194SourceRestoreOpen.runRestore args tail n (le_refl n)
  change F PA194SourceControllerCode.run ![PA194SourceRestoreOpen.three n,sourceState 31 args tail] = sourceState 31 mid tail at hrun
  have hexit := restoreExit mid tail hz
  change F (iterate PA194SourceControllerCode.step) ![(PA194SourceRestoreOpen.three n+1)+1,sourceState 31 args tail] = _
  rw [PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterSucc]
  change F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.run ![PA194SourceRestoreOpen.three n,sourceState 31 args tail]]] = _
  rw [hrun,hexit]

theorem freshSourceFetch (args : Fin 11 → M) (tail : M)
    (hl : args 8 = (0 : M)) (hx : args 6 = (0 : M)) :
    let n := args 0
    let dc := PA194SourceDrainOpen.four n+1
    let rc := (PA194SourceRestoreOpen.three n+1)+1
    let out := Function.update (Function.update args 0 (n+1)) 8 n
    F PA194SourceControllerCode.run ![(1 : M)+(dc+rc),sourceState 25 args tail] = sourceState 34 out tail := by
  let n := args 0
  let dc := PA194SourceDrainOpen.four n+1
  let rc := (PA194SourceRestoreOpen.three n+1)+1
  let dargs := PA194SourceDrainOpen.argsAt args n
  let mid := PA194SourceRestoreOpen.argsAt dargs (dargs 6)
  let out := Function.update (Function.update args 0 (n+1)) 8 n
  have h6 : dargs 6 = n := by simp [dargs,n,PA194SourceDrainOpen.argsAt,hx]
  have h0 : dargs 0 = (0 : M) := by simp [dargs,n,PA194SourceDrainOpen.argsAt,subSelf]
  have hout : Function.update mid 0 (mid 0+1) = out := by
    funext i
    fin_cases i <;> simp [mid,out,dargs,PA194SourceDrainOpen.argsAt,
      PA194SourceRestoreOpen.argsAt,n,subSelf,hl,hx,add_assoc]
  have hstart := sourceZero25 args tail hl
  have hd := drainExit args tail
  have hr := restoreComplete dargs tail
  change F PA194SourceControllerCode.run ![dc,sourceState 27 args tail] = sourceState 31 dargs tail at hd
  rw [h6] at hr
  have hmid : mid = PA194SourceRestoreOpen.argsAt dargs n := by dsimp [mid]; rw [h6]
  change F PA194SourceControllerCode.run ![rc,sourceState 31 dargs tail] =
    sourceState 34 (Function.update (PA194SourceRestoreOpen.argsAt dargs n) 0
      ((PA194SourceRestoreOpen.argsAt dargs n) 0+1)) tail at hr
  rw [←hmid,hout] at hr
  change F (iterate PA194SourceControllerCode.step) ![(1 : M)+(dc+rc),sourceState 25 args tail] = _
  rw [PA194IterateAddOpen.iterateAdd]
  have hone : F (iterate PA194SourceControllerCode.step) ![(1 : M),sourceState 25 args tail] = F PA194SourceControllerCode.step ![sourceState 25 args tail] := by
    have hz : (1 : M) = (0 : M)+1 := (zero_add _).symm
    rw [hz,PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterZero]
  rw [hone,hstart]
  rw [PA194IterateAddOpen.iterateAdd]
  change F PA194SourceControllerCode.run ![rc,F PA194SourceControllerCode.run ![dc,sourceState 27 args tail]] = _
  rw [hd,hr]

#print axioms drainExit
#print axioms restoreComplete
#print axioms freshSourceFetch
end models
end PA194SourceFetchOpen
