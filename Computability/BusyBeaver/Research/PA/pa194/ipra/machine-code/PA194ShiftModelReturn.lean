import PA194ShiftModelPreGuard
import PA194ShiftModelGuardReturn
import PA194ModelShiftReader
import PA194SchedulerSourceFrame

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

namespace PA194ShiftModelReturn
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceFetchLoop
open PA194SourceFetchRestoreLoop PA194SourceControllerStep PA194IteratedSimulation


open PA194ModelMPDrain PA194ModelMPTransfer

open PA194ShiftModelPreGuard PA194MachineProjections PA194SchedulerCode PA194MachineShiftMPCode
open PA194SchedulerIteration (fN fL fT fW fD fH haltAt pack_model fst_model snd_model step_fields)
open PA194SchedulerSourceFrame

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
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def returnArgs (args : Fin 11 → M) : Fin 11 → M :=
  Function.update
    (Function.update (store args (args 5) (F fixedFirst ![args 2]) 0)
      2 (F fixedSecond ![args 2])) 7 0

theorem shiftReturns (args : Fin 11 → M) (suffix : M)
    (hx : args 6 = 0) (hy : args 7 = 0) (hguard : args 1+args 5 ≠ 1) :
    ReachesPositive (sourceState 3661 args suffix) (sourceState 25 (returnArgs args) suffix) := by
  let pre := store args (args 5) (args 1+args 5) (0 : M)
  let cleared := Function.update pre 5 (0 : M)
  have h1 := runToGuard args suffix hx
  have hpre : pre 6 = (0 : M) := by simp [pre,store]
  have hcache : pre 5 ≠ (1 : M) := by simpa [pre,store] using hguard
  have h2 := PA194ShiftModelGuardReturn.guardReturns pre suffix hpre hcache
  have hclear6 : cleared 6 = (0 : M) := by simp [cleared,pre,store]
  have hclear7 : cleared 7 = (0 : M) := by simp [cleared,pre,store,hy]
  have h3 := PA194ModelShiftReader.execute cleared suffix hclear6 hclear7
  let decoded := Function.update (Function.update (Function.update
    (Function.update cleared 2 (F fixedSecond ![cleared 2]))
    5 (cleared 5+F fixedFirst ![cleared 2])) 6 0) 7 0
  have hout : decoded = returnArgs args := by
    funext i
    fin_cases i <;> simp [decoded,cleared,pre,store,returnArgs]
  change ReachesPositive (sourceState 11 cleared suffix) (sourceState 25 decoded suffix) at h3
  rw [hout] at h3
  exact appendPositive (append h1.reaches h2.reaches) h3

theorem nextShiftFields (s : M) (hshift : F (head fN fL) ![s] = (0 : M)) :
    let ns := F PA194SchedulerIteration.step ![s]
    F fL ![ns] = F (PA194SchedulerCode.tail fN fL) ![s] ∧
    F fT ![ns] = F fH ![s] ∧
    F fW ![ns] = F fixedSecond ![F fW ![s]] ∧
    F fD ![ns] = F fD ![s] ∧
    F fH ![ns] = F fixedFirst ![F fW ![s]] := by
  let ns := F PA194SchedulerIteration.step ![s]
  have hv (z : M) : (fun _ : Fin 1 => z) = ![z] := by
    funext i
    fin_cases i
    rfl
  have l : F fL ![ns] = F (nextL fN fL) ![s] := by
    simp only [ns,PA194SchedulerIteration.step,pack_model,fL,fst_model,snd_model,
      modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  have d : F fD ![ns] = F (nextD fN fL fD) ![s] := by
    simp only [ns,PA194SchedulerIteration.step,pack_model,fD,fst_model,snd_model,
      modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  obtain ⟨ht,hw,hh⟩ := step_fields s
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [l,nextL,choose0_model,if_pos hshift]
  · rw [ht,nextTop,choose0_model,if_pos hshift]
  · rw [hw,nextStack,choose0_model,if_pos hshift,shiftStack,PA194PathIterator.modelUnary,hv]
  · rw [d,nextD,choose0_model,if_pos hshift]
  · rw [hh,nextCache,choose0_model,if_pos hshift,shiftCache,PA194PathIterator.modelUnary,hv]

/-- A SHIFT with a clear halt flag runs from one aligned scheduler frame to
the next, including the updated command suffix. -/
theorem fromSchedulerFrame (s : M) (htag : F (head fN fL) ![s] = (0 : M))
    (hflag : F haltAt ![s] ≠ 1) :
    ReachesPositive (F frame ![s]) (F frame ![F PA194SchedulerIteration.step ![s]]) := by
  simp only [frame_model]
  obtain ⟨clock,out,hprefix,hhead,hL,hN,h6,h7,hkeep⟩ :=
    PA194SchedulerDispatchOpen.fetchDecodeDispatchPreserving s (arguments s) 0
      rfl rfl rfl rfl rfl
  have h1 := hkeep 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h2 := hkeep 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h4 := hkeep 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 := hkeep 5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h9 := hkeep 9 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h10 := hkeep 10 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsum : out 1+out 5 ≠ (1 : M) := by
    rw [h1,h5]
    intro hs
    exact hflag ((PA194SchedulerHaltSource.haltFlag_iff s).mpr ⟨htag,hs⟩)
  have hclear : out 3 = (0 : M) := hhead.symm.trans htag
  have hshift := PA194DispatchTag.shiftTag out (0 : M) hclear
  obtain ⟨hnl,hnt,hnw,hnd,hnh⟩ := nextShiftFields s htag
  have hret := shiftReturns out (0 : M) h6 h7 hsum
  have eq : returnArgs out = arguments (F PA194SchedulerIteration.step ![s]) := by
    funext i
    fin_cases i <;>
      simp [returnArgs,store,arguments,hN,hL,hnl,hnt,hnw,hnd,hnh,h1,h2,h4,h5,h9,h10,hclear]
  rw [eq] at hret
  exact appendPositive (append ⟨clock,hprefix⟩ (oneStep hshift).reaches) hret

#print axioms shiftReturns
#print axioms nextShiftFields
#print axioms fromSchedulerFrame
end models
end PA194ShiftModelReturn
