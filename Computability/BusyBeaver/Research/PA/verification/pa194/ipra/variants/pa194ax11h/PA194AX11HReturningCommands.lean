import PA194AX11HShiftFrame
import PA194AX11HMPSchedulerLink
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194AX11HReturningCommands
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

theorem advance
    (axiomBranch : ∀ (s k : M), F (head fN fL) ![s] = (k+1)+1 →
      ∃ n : M, 0 < n ∧ F (iterate PA194AX11HSource.step) ![n,F frame ![s]] =
        F frame ![F (stepK .top true) ![s]])
    (s : M) (clear : F (haltAtK true) ![s] ≠ 1) :
    ∃ n : M, 0 < n ∧ F (iterate PA194AX11HSource.step) ![n,F frame ![s]] =
      F frame ![F (stepK .top true) ![s]] := by
  rcases zero_or_succ (F (head fN fL) ![s]) with hz | ⟨n, hn⟩
  · exact PA194AX11HShiftFrame.advance s hz clear
  · rcases zero_or_succ n with hz | ⟨k, hk⟩
    · exact PA194AX11HMPSchedulerLink.advance s (by simpa [hz] using hn)
    · exact axiomBranch s k (by rwa [hk] at hn)

#print axioms advance
end models
end PA194AX11HReturningCommands
