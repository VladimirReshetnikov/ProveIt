import PA194DecoderComplete
import PA194SchedulerFetchModel
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194SchedulerDecode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch PackedClock PackedRootModel
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194IteratedSimulation PA194ControllerRunAdd PA194DecoderSynchronization PA194DecoderClock PA194DecoderComplete
open PA194SchedulerCode PA194SchedulerIteration PA194SchedulerFetchModel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fetchAndDecode (scheduler : M) (initial : Fin 11 → M) (tail : M)
    (hn : F fN ![scheduler] = initial 0) (hl : F fL ![scheduler] = initial 8)
    (hx : initial 6 = (0 : M)) (hy : initial 7 = (0 : M)) :
    ∃ (clock : M) (out : Fin 11 → M),
      F PA194SourceControllerCode.run ![clock,sourceState 25 initial tail] = sourceState 42 out tail ∧
      F (head fN fL) ![scheduler] = out 6 ∧
      F (PA194SchedulerCode.tail fN fL) ![scheduler] = out 7 ∧
      F fN ![F PA194SchedulerIteration.step ![scheduler]] = out 0 ∧ out 8 = 0 := by
  obtain ⟨t,mid,hfetch,hseed,hN,hxmid,hother⟩ := fetchPrefix scheduler initial tail hn hl hx
  have hymid : mid 7 = (0 : M) := by
    have h := hother (7 : Fin 11) (by decide) (by decide)
    simpa [hy] using h
  obtain ⟨x,y,hdecode,hfirst,hsecond⟩ := decodeFromZero mid tail hxmid hymid
  let out := argsAt mid x y (0 : M)
  let tdecode := F totalClock ![mid 8,sourceState 34 mid tail]+1
  have hfirst' : F (head fN fL) ![scheduler] = x := by
    rw [head,PA194PathIterator.modelUnary]
    have hv : (fun _ : Fin 1 => F (fetchSeed fN fL) ![scheduler]) = ![F (fetchSeed fN fL) ![scheduler]] := by
      funext i; fin_cases i; rfl
    rw [hv,hseed]
    exact hfirst
  have hsecond' : F (PA194SchedulerCode.tail fN fL) ![scheduler] = y := by
    rw [PA194SchedulerCode.tail,PA194PathIterator.modelUnary]
    have hv : (fun _ : Fin 1 => F (fetchSeed fN fL) ![scheduler]) = ![F (fetchSeed fN fL) ![scheduler]] := by
      funext i; fin_cases i; rfl
    rw [hv,hseed]
    exact hsecond
  refine ⟨t+tdecode,out,?_,?_,?_,?_,?_⟩
  · change F (iterate PA194SourceControllerCode.step) ![t+tdecode,sourceState 25 initial tail] = _
    rw [PA194ControllerRunAdd.iterateAdd]
    change F PA194SourceControllerCode.run ![tdecode,F PA194SourceControllerCode.run ![t,sourceState 25 initial tail]] = _
    rw [hfetch]
    exact hdecode
  · simpa [out,argsAt] using hfirst'
  · simpa [out,argsAt] using hsecond'
  · simpa [out,argsAt] using hN
  · simp [out,argsAt]
#print axioms fetchAndDecode
end models
end PA194SchedulerDecode
