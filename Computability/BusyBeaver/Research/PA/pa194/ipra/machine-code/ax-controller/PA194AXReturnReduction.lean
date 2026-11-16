import PA194ShiftModelReturn
import PA194ModelMPFromFrame
import PA194NativeControllerCorrectness

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194AXReturnReduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAHerbrandSelection TableDispatch
open PA194SchedulerIteration PA194SchedulerCode PA194MachineShiftMPCode
open PA194SchedulerSourceFrame PA194ModelMPDrain

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

/-- The remaining AX command contract, stated at the exact scheduler frame. -/
def AXReturns : Prop :=
  ∀ s c : M, F (head fN fL) ![s] = (c+1)+1 →
    ReachesPositive (F frame ![s]) (F frame ![F PA194SchedulerIteration.step ![s]])

theorem commandsReturn (ax : AXReturns (M := M)) (s : M)
    (hflag : F haltAt ![s] ≠ (1 : M)) :
    ReachesPositive (F frame ![s]) (F frame ![F PA194SchedulerIteration.step ![s]]) := by
  rcases zero_or_succ (F (head fN fL) ![s]) with htag | ⟨q,hq⟩
  · exact PA194ShiftModelReturn.fromSchedulerFrame s htag hflag
  · rcases zero_or_succ q with hq0 | ⟨c,hc⟩
    · exact PA194ModelMPFromFrame.advance s (by simpa only [hq0,zero_add] using hq)
    · exact ax s c (by simpa only [hc] using hq)

/-- On the literal machine, the AX return contract suffices to identify
its halting sentence with a halt of the modeled scheduler. -/
theorem literal_iff_scheduler (ax : AXReturns (M := M)) :
    (M↓[language] ⊧ PA194ExplicitEndpoint.haltClassical) ↔
      ∃ n : M, F haltAt ![F PA194SchedulerIteration.run ![n,F initial Fin.elim0]] = 1 := by
  exact PA194NativeControllerCorrectness.endpoint.trans
    (equivalent_of_return (commandsReturn ax))

#print axioms commandsReturn
#print axioms literal_iff_scheduler
end models
end PA194AXReturnReduction
