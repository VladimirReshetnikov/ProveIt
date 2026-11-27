import PA194M5FetchScheduler
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194M5DecodeScheduler
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

theorem fetchDecode (s : M) (a : Fin 11 → M) (tail : M)
    (hn : F fN ![s] = a 0) (hl : F fL ![s] = a 8)
    (hx : a 6 = 0) (hy : a 7 = 0) (h3 : a 3 = 0) :
    ∃ out : Fin 11 → M,
      PA194PausedReach.Reaches (PA194ProgramDrain.step PA194M5Program.program) (sourceState 25 a tail) (sourceState 48 out tail) ∧
      F (head fN fL) ![s] = out 3 ∧ F (PA194SchedulerCode.tail fN fL) ![s] = out 8 ∧
      F (nextN fN fL) ![s] = out 0 ∧ out 6 = 0 ∧ out 7 = 0 ∧
      ∀ i : Fin 11, i ≠ 0 → i ≠ 3 → i ≠ 6 → i ≠ 7 → i ≠ 8 → out i = a i := by
  obtain ⟨mid,hreach,hseed,hN,hX,other⟩ := PA194M5FetchScheduler.fetchPrefix s a tail hn hl hx
  have hY : mid 7 = 0 := by simpa [hy] using other 7 (by decide) (by decide)
  have h3' : mid 3 = 0 := by simpa [h3] using other 3 (by decide) (by decide)
  let out := PA194M5FetchReader.output mid
  have hdecode := PA194M5FetchReader.reader mid tail hX hY
  have hhead : F (head fN fL) ![s] = F fixedFirst ![mid 8] := by
    rw [head,PA194PathIterator.modelUnary]
    have hv : (fun _ : Fin 1 => F (fetchSeed fN fL) ![s]) = ![F (fetchSeed fN fL) ![s]] := by funext i; fin_cases i; rfl
    rw [hv,hseed]
  have htail : F (PA194SchedulerCode.tail fN fL) ![s] = F fixedSecond ![mid 8] := by
    rw [PA194SchedulerCode.tail,PA194PathIterator.modelUnary]
    have hv : (fun _ : Fin 1 => F (fetchSeed fN fL) ![s]) = ![F (fetchSeed fN fL) ![s]] := by funext i; fin_cases i; rfl
    rw [hv,hseed]
  refine ⟨out,PA194PausedReach.append _ hreach hdecode,?_,?_,?_,?_,?_,?_⟩
  · simpa [out,PA194M5FetchReader.output,h3'] using hhead
  · simpa [out,PA194M5FetchReader.output] using htail
  · rw [←PA194SchedulerFieldsOpen.packedNextN]
    simpa [out,PA194M5FetchReader.output] using hN
  · simpa [out,PA194M5FetchReader.output] using hX
  · simpa [out,PA194M5FetchReader.output] using hY
  · intro i hi0 hi3 hi6 hi7 hi8
    simpa [out,PA194M5FetchReader.output,Function.update_of_ne hi3,Function.update_of_ne hi8] using other i hi0 hi8
#print axioms fetchDecode
end models
end PA194M5DecodeScheduler
