import PA194AX11HPushOriginalReach
import PA194FirstActualPush
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HPushExact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourcePCBound PA194FiniteControls PA194StateOne
open PA194SchedulerFetchPositive PA194SourceFetchLoop PA194ModelMPPush PA194IteratedSimulation
open PA194AX11HPushPaused PA194AX11HPushIterationExtra PA194AX11HPushOriginal PA194FirstActualPush
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

/-- The literal revised push reaches the exact expected file at its first exit. -/
theorem revised_push_exact (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    ∃ n : M, F (iterate PA194AX11HSource.step) ![n,sourceState 3553 a tail] =
      sourceState 3572 (pushed a) tail := by
  have halign : aligned (sourceState 3568 a tail) (sourceState 3553 a tail) := by
    refine ⟨0,?_,?_,?_,?_⟩
    · exact modelNumeralStrict 0 20 (by decide)
    · rw [statePC,add_zero]
    · rw [statePC,add_zero]
    · simp only [sourceState,pi₂_pair]
  obtain ⟨n,hexact,hprior⟩ := first_actual_push a tail hx hy
  have hr := actual_runs_until_original_exit (sourceState 3568 a tail) (sourceState 3553 a tail) n halign hprior
  have hpair := source_orbit_aligned n (sourceState 3568 a tail) (sourceState 3553 a tail) halign
  have hrelation : aligned (F (iterate PA194SourceControllerCode.step) ![n,sourceState 3568 a tail])
      (F (iterate PA194AX11HSource.step) ![n,sourceState 3553 a tail]) := by
    rw [hr.1,hr.2]; exact hpair
  have hpc : F pc ![F (iterate PA194AX11HSource.step) ![n,sourceState 3553 a tail]] = modelNumeral M 3572 := by
    apply (aligned_exit_iff _ _ hrelation).mp
    rw [hexact]
    exact statePC 3587 (pushed a) tail
  obtain ⟨_,_,_,_,hfiles⟩ := hrelation
  rw [hexact] at hfiles
  rw [pcModel] at hpc
  refine ⟨n,?_⟩
  calc
    F (iterate PA194AX11HSource.step) ![n,sourceState 3553 a tail] =
        pair (pi₁ (F (iterate PA194AX11HSource.step) ![n,sourceState 3553 a tail]))
          (pi₂ (F (iterate PA194AX11HSource.step) ![n,sourceState 3553 a tail])) := (pair_unpair _).symm
    _ = sourceState 3572 (pushed a) tail := by
      rw [hpc,←hfiles]
      simp [sourceState]

#print axioms revised_push_exact
end models
end PA194AX11HPushExact
