import PA194AXReturnReduction
import PA194ModelAXBody
import PA194AXModelValues
import PA194ModelAXFromFrame

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194LiteralSchedulerCorrectness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAHerbrandSelection TableDispatch
open PA194SchedulerIteration PA194SchedulerCode PA194MachineShiftMPCode
open PA194SchedulerSourceFrame PA194ModelMPDrain PA194AXReturnReduction

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

theorem axBody : PA194ModelAXFromFrame.Body (M := M) := by
  intro a suffix hx hy
  have h := PA194ModelAXBody.execute a suffix hx hy
  rw [PA194AXModelValues.body_evaluation a hx hy] at h
  exact h.reaches

theorem axReturns : AXReturns (M := M) := by
  intro s c htag
  exact PA194ModelAXFromFrame.advance s c htag axBody

/-- Literal blank-tape halting coincides with halting of the modeled
scheduler in every candidate PRA model with IΣ₁ arithmetic reduct. -/
theorem endpoint :
    (M↓[language] ⊧ PA194ExplicitEndpoint.haltClassical) ↔
      ∃ n : M, F haltAt ![F PA194SchedulerIteration.run ![n,F initial Fin.elim0]] = 1 :=
  literal_iff_scheduler axReturns

#print axioms axBody
#print axioms axReturns
#print axioms endpoint
end models
end PA194LiteralSchedulerCorrectness
