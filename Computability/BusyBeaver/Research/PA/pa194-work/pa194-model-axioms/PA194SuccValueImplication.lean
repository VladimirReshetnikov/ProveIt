import PA194SuccValueCode
import PA194ValueDomain
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194SuccValueSchema
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194Schematic PA194GuardedCompiler PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (T : Theory SourceL) [T.Δ₁]

theorem succValueImplication (s : V) (hs : IsSemiterm PA194PAeq.language 0 s) :
    Provable T (neg SourceL succTotalCode ^⋎
      (neg SourceL (^∃ (valBody s)) ^⋎ (^∃ (valBody (succT s))))) := by
  obtain ⟨r,heq,hr⟩ := valBody_has_domain s hs
  have h := inst_provable_of_valid (σ r hr) T schema schema_valid
  change Provable T (instS (σ r hr) schema).val at h
  rw [instance_code s r hs hr heq] at h
  exact h
#print axioms succValueImplication
end generic
end PA194SuccValueSchema
