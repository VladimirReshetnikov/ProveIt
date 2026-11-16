import PA194BSegment
import ConPAMachineStutter

/-! The literal PA194B halting sentence has the same meaning as the primary
table's sentence in every model of IΣ₁. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace PA194BSimulation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ConPA.Machine

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem haltRuns :
    (∃ t : V, π₁ (run variantTable t) = (194 : V)) ↔
      (∃ n : V, π₁ (run primaryTable n) = (194 : V)) :=
  Stutter.equivalent primaryTable variantTable 194 194 (Relation (V := V))
    relationDef initial (fun _ _ h => halt_iff h) variantFixed (fun _ _ h _ => segment h)

theorem haltModels :
    (haltDef variantTable 194).val.Evalb (M := V) ![] ↔
      (haltDef primaryTable 194).val.Evalb (M := V) ![] :=
  (haltDef_iff variantTable 194).trans ((haltRuns (V := V)).trans (haltDef_iff primaryTable 194).symm)

#print axioms haltRuns
#print axioms haltModels
end models
end PA194BSimulation
