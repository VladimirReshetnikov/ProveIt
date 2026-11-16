import PA194SchedulerDecodeOpen
import PA194DispatchTransfersOpen
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194SchedulerDispatchOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch PackedClock PackedRootModel
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194IteratedSimulation PA194IterateAddOpen PA194DecoderSynchronizationOpen PA194DecoderClock PA194DecoderCompleteOpen
open PA194SchedulerCode PA194SchedulerIteration PA194SchedulerFetchOpen PA194DispatchTransfersOpen
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem fetchDecodeDispatchPreserving (scheduler : M) (initial : Fin 11 → M) (tail : M)
    (hn : F fN ![scheduler] = initial 0) (hl : F fL ![scheduler] = initial 8)
    (hx : initial 6 = (0 : M)) (hy : initial 7 = (0 : M)) (h3 : initial 3 = (0 : M)) :
    ∃ (clock : M) (out : Fin 11 → M),
      F PA194SourceControllerCode.run ![clock,sourceState 25 initial tail] = sourceState 48 out tail ∧
      F (head fN fL) ![scheduler] = out 3 ∧
      F (PA194SchedulerCode.tail fN fL) ![scheduler] = out 8 ∧
      F fN ![F PA194SchedulerIteration.step ![scheduler]] = out 0 ∧ out 6 = 0 ∧ out 7 = 0 ∧
      ∀ i : Fin 11, i ≠ 0 → i ≠ 3 → i ≠ 6 → i ≠ 7 → i ≠ 8 → out i = initial i := by
  obtain ⟨t,mid,hfetch,hseed,hN,hxmid,hother⟩ := fetchPrefix scheduler initial tail hn hl hx
  have hymid : mid 7 = (0 : M) := by
    have h := hother (7 : Fin 11) (by decide) (by decide)
    simpa [hy] using h
  have h3mid : mid 3 = (0 : M) := by
    have h := hother (3 : Fin 11) (by decide) (by decide)
    simpa [h3] using h
  have hc0 : F PA194TargetCantor.fixedCantor ![(0 : M),(0 : M)] = (0 : M) := by
    rw [PA194TargetCantor.modelCantorSelected PA194TargetCantor.fixedCantor PA194TargetCantor.fixedCantor_certified]
    simp [SetTheory.BusyBeaver.ZFC.ArithmeticCantor.cantor,SetTheory.BusyBeaver.ZFC.ArithmeticCantor.triangle]
  have hp : F addCode ![F PA194TargetCantor.fixedCantor ![mid 6,mid 7],mid 8] = mid 8 := by
    rw [hxmid,hymid,hc0]
    change (0 : M)+mid 8 = mid 8
    exact zero_add _
  let x := F PA194MachineProjections.fixedFirst ![mid 8]
  let y := F PA194MachineProjections.fixedSecond ![mid 8]
  have hdecode := PA194DecoderCompleteOpen.decodeCode mid tail
  rw [hp] at hdecode
  let decoded := argsAt mid x y (0 : M)
  let mid45 := PA194Transfer42Open.argsAt decoded (decoded 7)
  let out := PA194Transfer45Open.argsAt mid45 (mid45 6)
  let tdecode := F totalClock ![mid 8,sourceState 34 mid tail]+1
  let ttransfer := (PA194Transfer42Open.three (decoded 7)+1)+(PA194Transfer45Open.three (decoded 6)+1)
  have hd3 : decoded 3 = (0 : M) := by simp [decoded,argsAt,h3mid]
  have hd6 : decoded 6 = x := by simp [decoded,argsAt]
  have hd7 : decoded 7 = y := by simp [decoded,argsAt]
  have hd8 : decoded 8 = (0 : M) := by simp [decoded,argsAt]
  have hd0 : decoded 0 = mid 0 := by simp [decoded,argsAt]
  have htransfer := transferToDispatch decoded tail
  change F PA194SourceControllerCode.run ![ttransfer,sourceState 42 decoded tail] = sourceState 48 out tail ∧ _ at htransfer
  have ht3 : out 3 = decoded 3+decoded 6 := htransfer.2.1
  have ht8 : out 8 = decoded 8+decoded 7 := htransfer.2.2.1
  have hout3 : out 3 = x := by rw [ht3,hd3,hd6,zero_add]
  have hout8 : out 8 = y := by rw [ht8,hd8,hd7,zero_add]
  have hout0 : out 0 = mid 0 := by
    have h := htransfer.2.2.2.2.2 (0 : Fin 11) (by decide) (by decide) (by decide) (by decide)
    rw [hd0] at h
    exact h
  have hfirst' : F (head fN fL) ![scheduler] = x := by
    rw [head,PA194PathIterator.modelUnary]
    have hv : (fun _ : Fin 1 => F (fetchSeed fN fL) ![scheduler]) = ![F (fetchSeed fN fL) ![scheduler]] := by funext i; fin_cases i; rfl
    rw [hv,hseed]
  have hsecond' : F (PA194SchedulerCode.tail fN fL) ![scheduler] = y := by
    rw [PA194SchedulerCode.tail,PA194PathIterator.modelUnary]
    have hv : (fun _ : Fin 1 => F (fetchSeed fN fL) ![scheduler]) = ![F (fetchSeed fN fL) ![scheduler]] := by funext i; fin_cases i; rfl
    rw [hv,hseed]
  refine ⟨t+(tdecode+ttransfer),out,?_,?_,?_,?_,htransfer.2.2.2.1,htransfer.2.2.2.2.1,?_⟩
  · change F (iterate PA194SourceControllerCode.step) ![t+(tdecode+ttransfer),sourceState 25 initial tail] = _
    rw [PA194IterateAddOpen.iterateAdd]
    change F (iterate PA194SourceControllerCode.step) ![tdecode+ttransfer,F PA194SourceControllerCode.run ![t,sourceState 25 initial tail]] = _
    rw [hfetch,PA194IterateAddOpen.iterateAdd]
    change F PA194SourceControllerCode.run ![ttransfer,F PA194SourceControllerCode.run ![tdecode,sourceState 34 mid tail]] = _
    rw [hdecode]
    exact htransfer.1
  · simpa [hout3] using hfirst'
  · simpa [hout8] using hsecond'
  · simpa [hout0] using hN
  · intro i h0i h3i h6i h7i h8i
    calc
      out i = decoded i := htransfer.2.2.2.2.2 i h3i h6i h7i h8i
      _ = mid i := by simp [decoded,argsAt,h6i,h7i,h8i]
      _ = initial i := hother i h0i h8i

theorem fetchDecodeDispatch (scheduler : M) (initial : Fin 11 → M) (tail : M)
    (hn : F fN ![scheduler] = initial 0) (hl : F fL ![scheduler] = initial 8)
    (hx : initial 6 = (0 : M)) (hy : initial 7 = (0 : M)) (h3 : initial 3 = (0 : M)) :
    ∃ (clock : M) (out : Fin 11 → M),
      F PA194SourceControllerCode.run ![clock,sourceState 25 initial tail] = sourceState 48 out tail ∧
      F (head fN fL) ![scheduler] = out 3 ∧
      F (PA194SchedulerCode.tail fN fL) ![scheduler] = out 8 ∧
      F fN ![F PA194SchedulerIteration.step ![scheduler]] = out 0 ∧ out 6 = 0 ∧ out 7 = 0 := by
  obtain ⟨clock,out,hr,hhead,htail,hn',hx',hy',_⟩ :=
    fetchDecodeDispatchPreserving scheduler initial tail hn hl hx hy h3
  exact ⟨clock,out,hr,hhead,htail,hn',hx',hy'⟩

#print axioms fetchDecodeDispatchPreserving
#print axioms fetchDecodeDispatch
end models
end PA194SchedulerDispatchOpen
