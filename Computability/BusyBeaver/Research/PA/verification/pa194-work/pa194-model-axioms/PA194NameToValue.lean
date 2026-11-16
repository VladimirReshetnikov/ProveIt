import PA194NameValueCode
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194NameValueSchema
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194Schematic PA194GuardedCompiler PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (T : Theory SourceL) [T.Δ₁]

theorem nameToValue (s : V) (hs : IsSemiterm PA194PAeq.language 0 s) :
    Provable T (neg SourceL (tr (exName s)) ^⋎ (^∃ (valBody s))) := by
  have h := inst_provable_of_valid (σ s hs) T schema schema_valid
  change Provable T (instS (σ s hs) schema).val at h
  rw [instance_code s hs] at h
  exact h
#print axioms nameToValue
end generic
end PA194NameValueSchema
