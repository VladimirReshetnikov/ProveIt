import PA194AX11HPushIterationExtra
import PA194IteratedSimulation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HPushOriginal
open PA194IteratedSimulation
open PA194AX11HPushIterationExtra
open PA194AX11HPushIteration
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PA194PathIterator
open PA194SourceControllerCode PA194SchedulerIteration PA194AX11HPushPaused PA194AX11HPushAlignedDef PA194StackCode PA194FiniteControls

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

theorem iterate_def (code : Code 1) (s : M) :
    𝚺₁-Function₁ (fun k : M => F (iterate code) ![k,s]) := by
  have h : 𝚺₁.DefinableFunction (fun e : Fin 2 → M => F (iterate code) e) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) (iterate code))
  have hf : 𝚺₁-Function₂ (fun k s : M => F (iterate code) ![k,s]) := by
    convert h using 1
    funext e
    exact congrArg (fun e : Fin 2 → M => F (iterate code) e) (Matrix.fun_eq_vec_two e).symm
  exact unary_from_binary _ s hf

/-- Prior to first exit, both projections are genuine unpaused source runs. -/
theorem actual_runs_until_original_exit (old revised n : M) (ha : aligned old revised)
    (hprior : ∀ j < n, F pc ![F (iterate PA194SourceControllerCode.step) ![j,old]] ≠ modelNumeral M 3587) :
    F (iterate PA194SourceControllerCode.step) ![n,old] = pi₁ (F pairedRun ![n,pair old revised]) ∧
    F (iterate PA194AX11HSource.step) ![n,revised] = pi₂ (F pairedRun ![n,pair old revised]) := by
  haveI := iterate_def (M := M) PA194SourceControllerCode.step old
  haveI := iterate_def (M := M) PA194AX11HSource.step revised
  haveI := pairedRun_def (M := M) (pair old revised)
  have hp : 𝚺₁-Predicate (fun k : M => k ≤ n →
      F (iterate PA194SourceControllerCode.step) ![k,old] = pi₁ (F pairedRun ![k,pair old revised]) ∧
      F (iterate PA194AX11HSource.step) ![k,revised] = pi₂ (F pairedRun ![k,pair old revised])) := by
    definability
  have hi : ∀ k : M, k ≤ n →
      F (iterate PA194SourceControllerCode.step) ![k,old] = pi₁ (F pairedRun ![k,pair old revised]) ∧
      F (iterate PA194AX11HSource.step) ![k,revised] = pi₂ (F pairedRun ![k,pair old revised]) := by
    intro k
    induction k using ISigma1.sigma1_succ_induction with
    | hP => exact hp
    | zero =>
      intro _
      simp only [iterateZero,source_orbit_base,pi₁_pair,pi₂_pair, and_self]
    | succ k ih =>
      intro hk
      have hklt : k < n := lt_of_lt_of_le (lt_add_one k) hk
      have hkle : k ≤ n := le_trans (le_add_of_nonneg_right (show (0:M) ≤ 1 from zero_le)) hk
      have hkprev := ih hkle
      have hlive := hprior k hklt
      rw [hkprev.1] at hlive
      rw [iterateSucc,iterateSucc,source_orbit_succ_live k old revised ha hlive,pi₁_pair,pi₂_pair]
      rw [hkprev.1,hkprev.2]
      exact ⟨rfl,rfl⟩
  exact hi n le_rfl

#print axioms actual_runs_until_original_exit
end models
end PA194AX11HPushOriginal
