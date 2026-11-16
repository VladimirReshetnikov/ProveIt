import PA194AX11HSourceOrbit
import PA194SchedulerSourceFrame
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HInitialOrbit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194IteratedSimulation PA194SchedulerIteration
open PA194AX11HSourceOrbit
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

theorem site10_iff_scheduler (next flag : Code 1)
    (returning : ∀ s : M, F flag ![s] ≠ 1 →
      ∃ c : M, 0 < c ∧ F sourceRun ![c,F PA194SchedulerSourceFrame.frame ![s]] =
        F PA194SchedulerSourceFrame.frame ![F next ![s]])
    (halting : ∀ s : M, F flag ![s] = 1 →
      ∃ c : M, F pc ![F sourceRun ![c,F PA194SchedulerSourceFrame.frame ![s]]] = modelNumeral M 10) :
    (∃ t : M, F pc ![F sourceRun ![t,(PA194CompressedStartup.initialSource : M)]] = modelNumeral M 10) ↔
      ∃ n : M, F flag ![F (iterate next) ![n,F initial Fin.elim0]] = 1 := by
  exact equivalent_site10 next flag PA194SchedulerSourceFrame.frame
    (F initial Fin.elim0) PA194CompressedStartup.initialSource
    PA194SchedulerSourceFrame.frame_initial.symm PA194SchedulerSourceFrame.frame_pc returning halting
#print axioms site10_iff_scheduler
end models
end PA194AX11HInitialOrbit
