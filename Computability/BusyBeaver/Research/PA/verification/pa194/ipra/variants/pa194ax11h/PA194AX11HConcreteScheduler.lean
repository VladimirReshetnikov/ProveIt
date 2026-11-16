import PA194AX11HDropOrbit
import PA194SchedulerSourceFrame
import PA194ControllerSchedulerCore
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HConcreteScheduler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194IteratedSimulation PA194SchedulerIteration
open PA194AX11HSourceOrbit PA194ControllerScheduler
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Concrete AX11H scheduler calibration, conditional on its two source command contracts. -/
theorem site10_iff_scheduler
    (returning : ∀ s : M, F (haltAtK true) ![s] ≠ 1 →
      ∃ c : M, 0 < c ∧ F sourceRun ![c,F PA194SchedulerSourceFrame.frame ![s]] =
        F PA194SchedulerSourceFrame.frame ![F (stepK .top true) ![s]])
    (halting : ∀ s : M, F (haltAtK true) ![s] = 1 →
      ∃ c : M, F pc ![F sourceRun ![c,F PA194SchedulerSourceFrame.frame ![s]]] = modelNumeral M 10) :
    (∃ t : M, F pc ![F sourceRun ![t,(PA194CompressedStartup.initialSource : M)]] = modelNumeral M 10) ↔
      ∃ n : M, F (haltAtK true) ![F (iterate (stepK .top true)) ![n,F initial Fin.elim0]] = 1 := by
  exact equivalent_site10 (stepK .top true) (haltAtK true) PA194SchedulerSourceFrame.frame
    (F initial Fin.elim0) PA194CompressedStartup.initialSource
    PA194SchedulerSourceFrame.frame_initial.symm PA194SchedulerSourceFrame.frame_pc returning halting

/-- The same equivalence in the scheduler's native run-code form. -/
theorem site10_iff_runK
    (returning : ∀ s : M, F (haltAtK true) ![s] ≠ 1 →
      ∃ c : M, 0 < c ∧ F sourceRun ![c,F PA194SchedulerSourceFrame.frame ![s]] =
        F PA194SchedulerSourceFrame.frame ![F (stepK .top true) ![s]])
    (halting : ∀ s : M, F (haltAtK true) ![s] = 1 →
      ∃ c : M, F pc ![F sourceRun ![c,F PA194SchedulerSourceFrame.frame ![s]]] = modelNumeral M 10) :
    (∃ t : M, F pc ![F sourceRun ![t,(PA194CompressedStartup.initialSource : M)]] = modelNumeral M 10) ↔
      ∃ n : M, F (haltAtK true) ![F (runK .top true) ![n,F initial Fin.elim0]] = 1 := by
  exact PA194AX11HDropOrbit.site10_iff_drop_scheduler (stepK .top true) (haltAtK true) returning halting
#print axioms site10_iff_scheduler
#print axioms site10_iff_runK
end models
end PA194AX11HConcreteScheduler
