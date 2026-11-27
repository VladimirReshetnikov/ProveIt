import PA194M5FetchDecode
import PA194SchedulerFieldsOpen
import PA194SchedulerIteration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194M5FetchScheduler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SchedulerCode PA194SchedulerIteration
open PA194ModelMPDrain PA194TargetCantor PA194MachineProjections
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

theorem fetchPrefix (scheduler : M) (a : Fin 11 → M) (tail : M)
    (hn : F fN ![scheduler] = a 0) (hl : F fL ![scheduler] = a 8) (hx : a 6 = 0) :
    ∃ mid : Fin 11 → M,
      PA194PausedReach.Reaches (PA194ProgramDrain.step PA194M5Program.program) (sourceState 25 a tail) (sourceState 34 mid tail) ∧
      F (fetchSeed fN fL) ![scheduler] = mid 8 ∧
      F fN ![F PA194SchedulerIteration.step ![scheduler]] = mid 0 ∧ mid 6 = 0 ∧
      ∀ i : Fin 11, i ≠ 0 → i ≠ 8 → mid i = a i := by
  classical
  by_cases hz : a 8 = 0
  · let out := PA194M5FetchDecode.freshFile a
    have fields := PA194SchedulerFieldsOpen.freshFields scheduler (a 0) hn (hl.trans hz)
    have raw := PA194M5FetchPrefix.fresh a tail hz
    dsimp only at raw
    have heq : (let b := argsAfter a 0 [8,6] (a 0)
      Function.update (Function.update b 0 (b 0+b 6+1)) 6 0) = out := by
      funext i
      fin_cases i <;> simp [out,PA194M5FetchDecode.freshFile,argsAfter,location,tally,subSelf,hz,hx,
        PA194StateOne.modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl]
    rw [heq] at raw
    refine ⟨out,raw,?_,?_,?_,?_⟩
    · simpa [out,PA194M5FetchDecode.freshFile] using fields.1
    · simpa [out,PA194M5FetchDecode.freshFile] using fields.2
    · simp [out,PA194M5FetchDecode.freshFile,hx]
    · intro i hi0 hi8
      simp [out,PA194M5FetchDecode.freshFile,Function.update_of_ne hi0,Function.update_of_ne hi8]
  · let m := F predCode (fun _ => a 8)
    have hs : F Code.succ (fun _ => m) = a 8 := (modelZeroOrSuccPred (a 8)).resolve_left hz
    have hm : a 8=m+1 := hs.symm.trans (modelAddOne m).symm
    let out := Function.update a 8 m
    have fields := PA194SchedulerFieldsOpen.packedPositiveFields scheduler (a 0) m hn (hl.trans hm)
    refine ⟨out,PA194M5FetchPrefix.positive a tail m hm,?_,?_,?_,?_⟩
    · simpa [out] using fields.1
    · simpa [out] using fields.2
    · simp [out,hx]
    · intro i hi0 hi8
      simp [out,Function.update_of_ne hi8]

#print axioms fetchPrefix
end models
end PA194M5FetchScheduler
