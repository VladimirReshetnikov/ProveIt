import PA194AX11HGateWindow
import PA194AX11HPushOriginal
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HGateRun
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194FiniteControls PA194AX11HGateWindow
open PA194IteratedSimulation PA194AX11HPushOriginal
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

/-- The candidate and primary runs coincide for model-valued time n whenever
    the primary run remains within the AX-gate window for each earlier step. -/
theorem gate_runs_equal (seed n : M)
    (hwindow : ∀ j < n, ∃ k : M, k < modelNumeral M 34 ∧
      F pc ![F (iterate PA194SourceControllerCode.step) ![j,seed]] = modelNumeral M 3519 + k) :
    F (iterate PA194AX11HSource.step) ![n,seed] = F (iterate PA194SourceControllerCode.step) ![n,seed] := by
  haveI := iterate_def (M := M) PA194SourceControllerCode.step seed
  haveI := iterate_def (M := M) PA194AX11HSource.step seed
  have hp : 𝚺₁-Predicate (fun j : M => j ≤ n →
      F (iterate PA194AX11HSource.step) ![j,seed] = F (iterate PA194SourceControllerCode.step) ![j,seed]) := by
    definability
  have hi : ∀ j : M, j ≤ n →
      F (iterate PA194AX11HSource.step) ![j,seed] = F (iterate PA194SourceControllerCode.step) ![j,seed] := by
    intro j
    induction j using ISigma1.sigma1_succ_induction with
    | hP => exact hp
    | zero => intro _; rw [iterateZero,iterateZero]
    | succ j ih =>
      intro hj
      have hjlt : j < n := lt_of_lt_of_le (lt_add_one j) hj
      have hjle : j ≤ n := le_trans (le_add_of_nonneg_right (show (0:M) ≤ 1 from zero_le)) hj
      obtain ⟨k,hk,hpc⟩ := hwindow j hjlt
      have he := gate_step_bounded (F (iterate PA194SourceControllerCode.step) ![j,seed]) k hk hpc
      rw [iterateSucc,iterateSucc,ih hjle,he]
  exact hi n le_rfl

#print axioms gate_runs_equal
end models
end PA194AX11HGateRun
