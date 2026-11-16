import PA194AX11HHaltCommand
import PA194AX11HDecodeScheduler
import PA194SchedulerSourceFrame
import PA194AX11HCacheFlag

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194AX11HHaltFrame
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode (pc)
open PA194SchedulerFetchPositive PA194SourceFetchLoop
open PA194SchedulerCode PA194SchedulerIteration PA194SchedulerSourceFrame
open PA194IteratedSimulation

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

theorem reachesHalt (s : M)
    (opcode : F (head fN fL) ![s] = 0) (cache : F fH ![s] = 1) :
    ∃ c : M, F pc ![F (iterate PA194AX11HSource.step) ![c,F frame ![s]]] = modelNumeral M 10 := by
  let a := arguments s
  obtain ⟨out, fetch, tag, _, _, scratch, _, other⟩ :=
    PA194AX11HDecodeScheduler.fetchDecode s a (0 : M) rfl rfl rfl rfl rfl
  have hcache : out 5 = (1 : M) := by
    have h := other 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    simpa [a,arguments,cache] using h
  obtain ⟨b, halt⟩ := PA194AX11HHaltCommand.decoded out 0 (tag.symm.trans opcode) hcache scratch
  obtain ⟨c, hc⟩ := PA194PausedReach.append PA194AX11HSource.step fetch halt
  rw [frame_model]
  exact ⟨c, by rw [hc,statePC]⟩

theorem fromFlag (s : M)
    (halts : F (PA194ControllerScheduler.haltAtK true) ![s] = 1) :
    ∃ c : M, F pc ![F (iterate PA194AX11HSource.step) ![c,F frame ![s]]] = modelNumeral M 10 := by
  obtain ⟨opcode, cache⟩ := (PA194AX11HCacheFlag.halt_iff s).mp halts
  exact reachesHalt s opcode cache

#print axioms reachesHalt
#print axioms fromFlag
end models
end PA194AX11HHaltFrame
