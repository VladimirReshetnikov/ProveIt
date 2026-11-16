import PA194AX11HPrepOriginal
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HPrepOriginalReach
open PA194AX11HPrepOriginal PA194IteratedSimulation
open PA194AX11HPrepIterationExtra
open PA194AX11HPrepIteration
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PA194PathIterator
open PA194SourceControllerCode PA194SchedulerIteration PA194AX11HPrepPaused PA194AX11HPrepAlignedDef PA194StackCode PA194FiniteControls

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

theorem first_original_exit (old : M)
    (hexists : ∃ n : M, F pc ![F (iterate PA194SourceControllerCode.step) ![n,old]] = modelNumeral M 3624) :
    ∃ n : M, F pc ![F (iterate PA194SourceControllerCode.step) ![n,old]] = modelNumeral M 3624 ∧
      ∀ j < n, F pc ![F (iterate PA194SourceControllerCode.step) ![j,old]] ≠ modelNumeral M 3624 := by
  let q : M → Prop := fun n => F pc ![F (iterate PA194SourceControllerCode.step) ![n,old]] = modelNumeral M 3624
  have he (s : M) : F pc ![s] = pi₁ s := by
    rw [PA194SourceControllerCode.pc]
    convert PackedDecoderModel.modelDecodeLeft s using 1
    apply congrArg (fun e : Fin 1 → M => F PackedClock.decodeLeft e)
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  haveI := iterate_def (M := M) PA194SourceControllerCode.step old
  have hq : 𝚺₁-Predicate q := by
    unfold q
    simp_rw [he]
    definability
  obtain ⟨m,hm⟩ := hexists
  exact InductionOnHierarchy.least_number_sigma 𝚺 1 (P := q) hq hm

/-- An original block exit implies simultaneous aligned actual source exits. -/
theorem source_reaches_exit_of_original (old revised : M) (ha : aligned old revised)
    (hexists : ∃ n : M, F pc ![F (iterate PA194SourceControllerCode.step) ![n,old]] = modelNumeral M 3624) :
    ∃ n : M,
      aligned (F (iterate PA194SourceControllerCode.step) ![n,old])
        (F (iterate PA194AX11HSource.step) ![n,revised]) ∧
      F pc ![F (iterate PA194SourceControllerCode.step) ![n,old]] = modelNumeral M 3624 ∧
      F pc ![F (iterate PA194AX11HSource.step) ![n,revised]] = modelNumeral M 3642 := by
  obtain ⟨n,he,hprior⟩ := first_original_exit old hexists
  have hr := actual_runs_until_original_exit old revised n ha hprior
  have hb := source_orbit_aligned n old revised ha
  have he2 : F pc ![pi₂ (F pairedRun ![n,pair old revised])] = modelNumeral M 3642 := by
    apply (aligned_exit_iff _ _ hb).mp
    rw [←hr.1]
    exact he
  refine ⟨n,?_,he,?_⟩
  · rw [hr.1,hr.2]; exact hb
  · rw [hr.2]; exact he2

#print axioms first_original_exit
#print axioms source_reaches_exit_of_original
end models
end PA194AX11HPrepOriginalReach
