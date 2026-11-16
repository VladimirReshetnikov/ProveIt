import PA194SourceFetchModel
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SchedulerFetchModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194IteratedSimulation PA194SchedulerCode PA194SchedulerIteration PA194SchedulerPackedFetchPositive
open PA194SourceFetchModel
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

theorem runTwo (s : M) :
    F PA194SourceControllerCode.run ![(1 : M)+1,s] =
      F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![s]] := by
  change F (iterate PA194SourceControllerCode.step) ![(1 : M)+1,s] = _
  rw [iterateSucc]
  have hz : (1 : M) = (0 : M)+1 := (zero_add _).symm
  rw [hz,iterateSucc,iterateZero]

theorem fetchPrefix (scheduler : M) (args : Fin 11 → M) (tail : M)
    (hn : F fN ![scheduler] = args 0) (hl : F fL ![scheduler] = args 8)
    (hx : args 6 = (0 : M)) :
    ∃ (clock : M) (out : Fin 11 → M),
      F PA194SourceControllerCode.run ![clock,sourceState 25 args tail] = sourceState 34 out tail ∧
      F (fetchSeed fN fL) ![scheduler] = out 8 ∧
      F fN ![F PA194SchedulerIteration.step ![scheduler]] = out 0 ∧
      out 6 = (0 : M) ∧
      ∀ i : Fin 11, i ≠ 0 → i ≠ 8 → out i = args i := by
  classical
  by_cases hz : args 8 = (0 : M)
  · let n := args 0
    let clock := (1 : M)+((PA194SourceDrainInvariant.four n+1)+
      ((PA194SourceRestoreInvariant.three n+1)+1))
    let out := Function.update (Function.update args 0 (n+1)) 8 n
    have h := schedulerFreshFetch scheduler args tail hn (hl.trans hz) hz hx
    change F PA194SourceControllerCode.run ![clock,sourceState 25 args tail] = sourceState 34 out tail ∧
      F (fetchSeed fN fL) ![scheduler] = out 8 ∧
      F fN ![F PA194SchedulerIteration.step ![scheduler]] = out 0 at h
    refine ⟨clock,out,h.1,h.2.1,h.2.2,?_,?_⟩
    · simp [out,hx]
    · intro i hi0 hi8
      simp [out,Function.update_of_ne hi0,Function.update_of_ne hi8]
  · let m := F predCode (fun _ => args 8)
    have hs : F Code.succ (fun _ => m) = args 8 := (modelZeroOrSuccPred (args 8)).resolve_left hz
    have hm : args 8=m+1 := hs.symm.trans (modelAddOne m).symm
    let out := Function.update args 8 m
    have h := packedPositiveFetchPrefix scheduler args tail m hn hl hm
    refine ⟨(1 : M)+1,out,?_,?_,?_,?_,?_⟩
    · rw [runTwo]; exact h.1
    · simpa [out] using h.2.1
    · simpa [out] using h.2.2
    · simp [out,hx]
    · intro i hi0 hi8
      simp [out,Function.update_of_ne hi8]
#print axioms runTwo
#print axioms fetchPrefix
end models
end PA194SchedulerFetchModel
