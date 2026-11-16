import PA194AX11HPrepOriginalReach
import PA194PausedPrep
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HPrepExact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourcePCBound PA194FiniteControls PA194StateOne
open PA194SchedulerFetchPositive PA194SourceFetchLoop PA194ModelMPImp PA194IteratedSimulation
open PA194AX11HPrepPaused PA194AX11HPrepIterationExtra PA194AX11HPrepOriginal PA194PausedPrep
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

/-- The literal revised preparation reaches the exact expected file at its first exit. -/
theorem revised_prep_exact (a : Fin 11 → M) (tail h w : M) (hx : a 6 = 0) (hy : a 7 = 0)
    (hw : a 2 = SetTheory.BusyBeaver.ZFC.ArithmeticCantor.cantor h w) :
    ∃ n : M, F (iterate PA194AX11HSource.step) ![n,sourceState 3605 a tail] =
      sourceState 3642 (PA194PausedPrep.result a h w) tail := by
  have halign : aligned (sourceState 3587 a tail) (sourceState 3605 a tail) := by
    refine ⟨0,?_,?_,?_,?_⟩
    · exact modelNumeralStrict 0 38 (by decide)
    · rw [statePC,add_zero]
    · rw [statePC,add_zero]
    · simp only [sourceState,pi₂_pair]
  obtain ⟨n,hexact,hprior⟩ := first_actual_prep a tail h w hx hy hw
  have hr := actual_runs_until_original_exit (sourceState 3587 a tail) (sourceState 3605 a tail) n halign hprior
  have hpair := source_orbit_aligned n (sourceState 3587 a tail) (sourceState 3605 a tail) halign
  have hrelation : aligned (F (iterate PA194SourceControllerCode.step) ![n,sourceState 3587 a tail])
      (F (iterate PA194AX11HSource.step) ![n,sourceState 3605 a tail]) := by
    rw [hr.1,hr.2]; exact hpair
  have hpc : F pc ![F (iterate PA194AX11HSource.step) ![n,sourceState 3605 a tail]] = modelNumeral M 3642 := by
    apply (aligned_exit_iff _ _ hrelation).mp
    rw [hexact]
    exact statePC 3624 (PA194PausedPrep.result a h w) tail
  obtain ⟨_,_,_,_,hfiles⟩ := hrelation
  rw [hexact] at hfiles
  rw [pcModel] at hpc
  refine ⟨n,?_⟩
  calc
    F (iterate PA194AX11HSource.step) ![n,sourceState 3605 a tail] =
        pair (pi₁ (F (iterate PA194AX11HSource.step) ![n,sourceState 3605 a tail]))
          (pi₂ (F (iterate PA194AX11HSource.step) ![n,sourceState 3605 a tail])) := (pair_unpair _).symm
    _ = sourceState 3642 (PA194PausedPrep.result a h w) tail := by
      rw [hpc,←hfiles]
      simp [sourceState]

#print axioms revised_prep_exact
end models
end PA194AX11HPrepExact
