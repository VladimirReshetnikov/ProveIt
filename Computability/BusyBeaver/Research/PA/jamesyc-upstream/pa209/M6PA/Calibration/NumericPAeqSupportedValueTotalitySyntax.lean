module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermFreeSupport
public import M6PA.Calibration.NumericPAeqValueGuardedTotalitySyntax
@[expose] public section

/-! Supported semantic environments reuse the original finite domain guards and
value-existence formula. Source-code magnitude is not a coverage condition. -/
namespace M6.PA.NumericPAeqSupportedValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

def SupportedValueEnvironment (s b f t : V) : Prop :=
  IsSemitermVec language s 0 b ∧ IsSemitermVec language (len f) 0 f ∧
    IsSemiterm Presentation.language s t ∧ FreeSupported (len f) t
attribute [local irreducible] freeSupportedGraph
noncomputable def supportedValueEnvironmentGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “s b f t. ∃ k, !lenDef k f ∧ !((isSemitermVec language).sigma) s 0 b ∧
    !((isSemitermVec language).sigma) k 0 f ∧ !((isSemiterm Presentation.language).sigma) s t ∧
    !freeSupportedGraph k t”
theorem supportedValueEnvironment_graph (s b f t : V) :
    supportedValueEnvironmentGraph.val.Evalb ![s,b,f,t] ↔ SupportedValueEnvironment s b f t := by
  simp [supportedValueEnvironmentGraph,SupportedValueEnvironment,freeSupported_graph,Matrix.comp_vecCons'']

theorem inputDomain_valid {s b f t : V} (h:SupportedValueEnvironment s b f t) :
    IsFormula language (inputDomain s b f) := by
  apply IsSemiformula.and.mpr
  exact ⟨NumericPAeqValueDomainGuard.guard_vector_isSemiformula h.1,
    NumericPAeqValueDomainGuard.guard_vector_isSemiformula h.2.1⟩

theorem supportedValueEnvironment_child {s b f t u : V}
    (h:SupportedValueEnvironment s b f t) (hu:IsSemiterm Presentation.language s u)
    (hs:FreeSupported (len f) u) : SupportedValueEnvironment s b f u :=
  ⟨h.1,h.2.1,hu,hs⟩

#print axioms supportedValueEnvironment_graph
#print axioms inputDomain_valid
#print axioms supportedValueEnvironment_child
end M6.PA.NumericPAeqSupportedValueTotality

