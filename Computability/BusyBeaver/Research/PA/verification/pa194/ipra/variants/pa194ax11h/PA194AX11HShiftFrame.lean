import PA194AX11HDecodeScheduler
import PA194AX11HShiftCommand
import PA194AX11HShiftFields
import PA194AX11HCacheFlag
import PA194AX11HMPSchedulerLink
import PA194SchedulerSourceFrame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194AX11HShiftFrame
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SchedulerCode PA194SchedulerIteration
open PA194ModelMPDrain PA194TargetCantor PA194MachineProjections PA194ModelMPImp
open PA194SchedulerSourceFrame PA194SourceRegisterRelation PA194IteratedSimulation PA194ControllerScheduler PA194StateOne
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

theorem advance (s : M) (hshift : F (head fN fL) ![s] = 0)
    (hclear : F (haltAtK true) ![s] ≠ 1) :
    ∃ n : M, 0 < n ∧ F (iterate PA194AX11HSource.step) ![n,F frame ![s]] =
      F frame ![F (stepK .top true) ![s]] := by
  have hcache : F fH ![s] ≠ 1 :=
    fun h => hclear ((PA194AX11HCacheFlag.halt_iff s).mpr ⟨hshift,h⟩)
  let a := arguments s
  obtain ⟨out, fetch, tag, suffix, counter, scratch, scratch', other⟩ :=
    PA194AX11HDecodeScheduler.fetchDecode s a (0 : M) rfl rfl rfl rfl rfl
  have hop := tag.symm.trans hshift
  have oldCache : out 5 = F fH ![s] := by
    simpa [a,arguments] using other 5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have oldStack : out 2 = F fW ![s] := by
    simpa [a,arguments] using other 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have oldD : out 4 = F fD ![s] := by
    simpa [a,arguments] using other 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have run := PA194AX11HShiftCommand.decoded out (0 : M) hop
    (fun h => hcache (oldCache.symm.trans h)) scratch scratch'
  have fields := PA194AX11HShiftFields.nextFields s hshift (tail4 fN fL) (.zero 1)
    (axStackA true fT (axArg fN fL) fD fH (yArg fN fL) (xArg fN fL) fW)
    (zField true fN fL) (.zero 1)
  rw [PA194AX11HMPSchedulerLink.link] at fields
  obtain ⟨hn, hl, ht, hw, hd, hh⟩ := fields
  let ns := F (stepK .top true) ![s]
  let result := PA194AX11HShiftCommand.output out
  have registers : regsOfArgs result = regsOfArgs (arguments ns) := by
    funext i
    fin_cases i <;> simp [regsOfArgs,arguments,result,ns,PA194AX11HShiftCommand.output,
      counter,suffix,hop,oldCache,oldStack,oldD,hn,hl,ht,hw,hd,hh]
  have finish : sourceState 25 result (0 : M) = F frame ![ns] := by
    rw [frame_model]
    simp only [sourceState,registers]
  obtain ⟨n, hfetch⟩ := fetch
  have hn0 : n ≠ 0 := by
    intro hz
    subst n
    rw [iterateZero] at hfetch
    have hpc := congrArg (fun q => F pc ![q]) hfetch
    rw [PA194SourceFetchLoop.statePC,PA194SourceFetchLoop.statePC] at hpc
    exact (ne_of_lt (modelNumeralStrict 25 48 (by decide))) hpc
  obtain ⟨m, hrun⟩ := run
  rw [frame_model]
  refine ⟨n+m, lt_of_lt_of_le (lt_of_le_of_ne zero_le (Ne.symm hn0)) (le_add_of_nonneg_right zero_le), ?_⟩
  rw [PA194ControllerRunAdd.iterateAdd,hfetch,hrun]
  exact finish

#print axioms advance
end models
end PA194AX11HShiftFrame
