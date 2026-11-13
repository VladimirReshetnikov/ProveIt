module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueTotalitySyntax
public import M6PA.Calibration.NumericPAeqValueDomainGuardValidity
@[expose] public section

/-! Full finite-environment domain antecedent for future semantic totality.
Only syntax, graph, and guarded arity are asserted in this module. -/
namespace M6.PA.NumericPAeqValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

def ValueEnvironment (s b f t : V) : Prop :=
  IsSemitermVec language s 0 b ∧ IsSemitermVec language (len f) 0 f ∧
    IsSemiterm Presentation.language s t ∧ t≤len f
noncomputable def valueEnvironmentGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “s b f t. ∃ k, !lenDef k f ∧ !((isSemitermVec language).sigma) s 0 b ∧
    !((isSemitermVec language).sigma) k 0 f ∧ !((isSemiterm Presentation.language).sigma) s t ∧ t≤k”
theorem valueEnvironment_graph (s b f t : V) :
    valueEnvironmentGraph.val.Evalb ![s,b,f,t] ↔ ValueEnvironment s b f t := by
  simp [valueEnvironmentGraph,ValueEnvironment,Matrix.comp_vecCons'']

noncomputable def inputDomain (s b f : V) : V :=
  qqAnd (NumericPAeqValueDomainGuard.guard b s) (NumericPAeqValueDomainGuard.guard f (len f))
noncomputable def guardedTotalityCode (s b f t : V) : V :=
  imp language (inputDomain s b f) (valueTotalityCode b f t)
attribute [local irreducible] NumericPAeqValueDomainGuard.guardGraph valueTotalityGraph
noncomputable def guardedTotalityGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “out s b f t. ∃ k left right antecedent consequent,
    !lenDef k f ∧ !NumericPAeqValueDomainGuard.guardGraph left b s ∧
    !NumericPAeqValueDomainGuard.guardGraph right f k ∧ !qqAndDef antecedent left right ∧
    !valueTotalityGraph consequent b f t ∧ !(impGraph language) out antecedent consequent”
theorem guardedTotality_graph (out s b f t : V) :
    guardedTotalityGraph.val.Evalb ![out,s,b,f,t] ↔ out=guardedTotalityCode s b f t := by
  simp [guardedTotalityGraph,guardedTotalityCode,inputDomain,NumericPAeqValueDomainGuard.guard_graph,
    valueTotality_graph,Matrix.comp_vecCons'']

theorem inputDomain_valid {s b f t : V} (h:ValueEnvironment s b f t) :
    IsFormula language (inputDomain s b f) := by
  apply IsSemiformula.and.mpr
  exact ⟨NumericPAeqValueDomainGuard.guard_vector_isSemiformula h.1,
    NumericPAeqValueDomainGuard.guard_vector_isSemiformula h.2.1⟩
theorem guardedTotality_valid {s b f t : V} (h:ValueEnvironment s b f t) :
    IsFormula language (guardedTotalityCode s b f t) :=
  IsSemiformula.imp.mpr ⟨inputDomain_valid h,valueTotality_isSemiformula h.1 h.2.1 h.2.2.1 h.2.2.2⟩

#print axioms valueEnvironment_graph
#print axioms guardedTotality_graph
#print axioms inputDomain_valid
#print axioms guardedTotality_valid
end M6.PA.NumericPAeqValueTotality

