import PA194SELSegment
import ConPAMachineStutter

/-! The literal PA194SEL and primary PA194 runs halt together in every
model of IΣ₁. -/

set_option autoImplicit false

namespace PA194SELSimulation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
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
end PA194SELSimulation
